# adc_audio_tx.py -- ESP-NOW encrypted audio SENDER, ESP32-C3, MicroPython.  Save on the board as main.py
#
# Always transmitting (no button): ADC pin 4 -> DC removal -> IMA-ADPCM (4 bit) -> AES-256-CTR(ECB-based) + HMAC-SHA256
# -> ESP-NOW broadcast.  Pair it with adc_audio_rx.py + viewer_audio.html.
#
# Wiring: analog audio source -> GPIO4 (ADC1_CH4).  The input must stay inside 0..~2.5 V (ATTN_11DB on the
# C3), so bias an AC-coupled source to ~1.2 V.  A raw electret / MAX9814 / MAX4466 output is fine.
#
# Wire format (same crypto as the walkie-talkie script, plus 1 byte carrying the sample-rate index):
#   [sid 8][seq 4 BE][ciphertext 4 + FRAME/2][tag 8]          FRAME = 320 -> 184 bytes, 40 ms at 8 kHz
#   plaintext = [adpcm_pred int16 LE][adpcm_index u8][rate_idx u8][FRAME/2 ADPCM bytes]
#   counter block i = sid | seq | i (u32 BE), AES-256-ECB keystream XOR (= CTR, built on ECB: no CTR mode needed)
#   tag       = HMAC-SHA256(mac_key, sid|seq|ciphertext)[:8]   (encrypt-then-MAC)
#
# Sampling: the C3 has one core and ADC reads are not interrupt-safe, so the main loop samples against
# ticks_us() on a fixed time grid and runs one step of the previous frame's work (encode / encrypt / MAC /
# send) at evenly spaced points in the frame.  A step that stalls sampling leaves missed slots, which are
# filled by linear interpolation (the diagnostic line shows how many), so pitch and timing stay correct.

import os
import gc
import time
import array
import struct
import hashlib
import micropython
import network
import espnow
import cryptolib
from machine import Pin, ADC

# ======================= CONFIG =======================
# 32-byte shared key, 64 hex chars, SAME on sender and receiver.
# Generate one on a PC:  python -c "import os;print(os.urandom(32).hex())"
KEY_HEX = "f803703aa2d6b3bdd660e3c095f2a4e95a11b6bcf87cda30f10d90cae8a158ab"

CHANNEL = 1             # Wi-Fi channel, same on both units
LONG_RANGE = False      # True = ESP-NOW LR 500 kbps (same on both units, Espressif <-> Espressif only)
TX_POWER_DBM = 2        # ESP-NOW transmit power in dBm (MicroPython takes dBm, range 2..20)

ADC_PIN = 4             # GPIO4 = ADC1_CH4 on the ESP32-C3
LED = 8
LED_ON = 0              # 0 = active-low LED (SuperMini)

RATES = (8000, 10000, 12500, 16000, 20000, 4000, 5000, 6000)   # must match RATES in viewer_audio.html / receiver
SAMPLE_RATE = 0         # 0 = AUTO: measure the ADC at start-up and use the highest rate in RATES it can sustain
                        # (or force one of RATES; a too-high rate drops samples and shifts the pitch)
AUTO_MARGIN = 1.15      # auto mode: required headroom over the measured sampler-loop cost
MAX_GAP_FRAC = 0.10     # auto mode: at most this fraction of samples may be interpolated (time lost to jobs)
FRAME = 320             # samples per packet (40 ms at 8 kHz). Keep even, <= 452. Bigger = fewer sends/s
GAIN = 16               # input gain in 1/16 steps after DC removal: 16 = x1, 32 = x2, 8 = x0.5
GC_EVERY = 50           # run gc.collect() in a quiet slot every N packets
DIAG_S = 2              # print a diagnostic line every DIAG_S seconds (each print stalls sampling ~10 ms)
# ======================================================

KEY = bytes.fromhex(KEY_HEX)
if len(KEY) != 32 or KEY == bytes(32):
    raise ValueError("Set KEY_HEX to a random 32-byte key (64 hex chars)")
if SAMPLE_RATE and SAMPLE_RATE not in RATES:
    raise ValueError("SAMPLE_RATE must be one of %r" % (RATES,))
RATE_IDX = 0

HDR = 12
BODY = 4 + FRAME // 2
TAG = 8
PKT_LEN = HDR + BODY + TAG
if FRAME & 1 or PKT_LEN > 250:
    raise ValueError("FRAME must be even and give packets <= 250 bytes")
BCAST = b'\xff' * 6
DIAG_EVERY = 50                         # packets between diagnostic lines (set in set_rate)
MASK = 0x3FFFFFFF                       # ticks_us() wraps at 2**30
HALF = 0x20000000

# ---------------- crypto ----------------
_EK = hashlib.sha256(KEY + b'walkie-enc').digest()
_MK = hashlib.sha256(KEY + b'walkie-mac').digest()
_IPAD = bytes([b ^ 0x36 for b in _MK] + [0x36] * 32)
_OPAD = bytes([b ^ 0x5C for b in _MK] + [0x5C] * 32)

# ---------------- IMA ADPCM ----------------
_STEP = array.array('H', [
    7, 8, 9, 10, 11, 12, 13, 14, 16, 17, 19, 21, 23, 25, 28, 31, 34, 37, 41, 45, 50, 55, 60, 66,
    73, 80, 88, 97, 107, 118, 130, 143, 157, 173, 190, 209, 230, 253, 279, 307, 337, 371, 408,
    449, 494, 544, 598, 658, 724, 796, 876, 963, 1060, 1166, 1282, 1411, 1552, 1707, 1878, 2066,
    2272, 2499, 2749, 3024, 3327, 3660, 4026, 4428, 4871, 5358, 5894, 6484, 7132, 7845, 8630,
    9493, 10442, 11487, 12635, 13899, 15289, 16818, 18500, 20350, 22385, 24623, 27086, 29794,
    32767])


@micropython.viper
def _enc(src, n: int, out, st, tbl, gain: int) -> int:
    # src: n uint16 ADC samples (read_u16).  out: n/2 bytes.
    # st: int32[3] = [pred, index, dc*1024]  (dc = slow running mean, removed before encoding)
    s = ptr16(src)
    o = ptr8(out)
    t = ptr32(st)
    stp = ptr16(tbl)
    pred = int(t[0])
    idx = int(t[1])
    dcq = int(t[2])
    i = 0
    while i < n:
        raw = int(s[i])
        dcq += raw - (dcq >> 10)            # leaky integrator, corner ~1 Hz at 8 kHz
        x = ((raw - (dcq >> 10)) * gain) >> 4
        if x > 32767:
            x = 32767
        if x < -32768:
            x = -32768
        step = int(stp[idx])
        d = x - pred
        code = 0
        if d < 0:
            code = 8
            d = -d
        diff = step >> 3
        if d >= step:
            code |= 4
            d -= step
            diff += step
        step >>= 1
        if d >= step:
            code |= 2
            d -= step
            diff += step
        step >>= 1
        if d >= step:
            code |= 1
            diff += step
        if code & 8:
            pred -= diff
        else:
            pred += diff
        if pred > 32767:
            pred = 32767
        if pred < -32768:
            pred = -32768
        c7 = code & 7
        if c7 < 4:
            idx -= 1
        else:
            idx += (c7 - 3) * 2
        if idx < 0:
            idx = 0
        if idx > 88:
            idx = 88
        if i & 1:
            o[i >> 1] = int(o[i >> 1]) | (code << 4)
        else:
            o[i >> 1] = code
        i += 1
    t[0] = pred
    t[1] = idx
    t[2] = dcq
    return 0


@micropython.viper
def _xor(a, b, out, n: int) -> int:
    x = ptr8(a)
    y = ptr8(b)
    o = ptr8(out)
    i = 0
    while i < n:
        o[i] = int(x[i]) ^ int(y[i])
        i += 1
    return 0


@micropython.viper
def _mm(src, n: int, st) -> int:
    # st: int32[3] = [min, max, sum of (raw >> 4)] over the raw ADC samples, for the diagnostics
    s = ptr16(src)
    t = ptr32(st)
    lo = int(t[0])
    hi = int(t[1])
    sm = int(t[2])
    i = 0
    while i < n:
        v = int(s[i])
        if v < lo:
            lo = v
        if v > hi:
            hi = v
        sm += v >> 4
        i += 1
    t[0] = lo
    t[1] = hi
    t[2] = sm
    return 0


# ---------------- state / buffers (all preallocated) ----------------
e = led = adc = None
sid = b''
seq = 0
enc_st = array.array('i', [0, 0, 0])
bufA = array.array('H', bytes(FRAME * 2))
bufB = array.array('H', bytes(FRAME * 2))
src = bufA              # frame currently being encoded
pt = bytearray(BODY)    # plaintext
adp_mv = memoryview(pt)[4:]
pkt = bytearray(PKT_LEN)
pkt_mv = memoryview(pkt)
ct_mv = pkt_mv[HDR:HDR + BODY]
NB = (BODY + 15) // 16                  # AES blocks per packet
ctrbuf = bytearray(NB * 16)             # counter blocks: sid | seq | block index (CTR built on ECB:
ksbuf = bytearray(NB * 16)              # this MicroPython build has no cryptolib CTR mode)
ecb = None
p0 = i0 = 0
inner = b''
npk = 0
sta = None
send_err = 0
last_err = 0
mm_st = array.array('i', [65535, 0, 0])
dg = [0, 0, 0, 0]       # since the last diagnostic line: [max job us, which job, interpolated slots, longest gap in slots]
d_t = 0
d_npk = 0


def setup():
    global e, led, adc, sid, ecb, sta
    sta = network.WLAN(network.STA_IF)
    sta.active(True)
    try:
        if LONG_RANGE:
            sta.config(protocol=network.MODE_11B | network.MODE_11G |
                                network.MODE_11N | network.MODE_LR)
        sta.config(channel=CHANNEL)
    except Exception as ex:
        print('wifi config failed:', ex)
    e = espnow.ESPNow()
    e.active(True)
    if LONG_RANGE:
        try:
            e.config(rate=0x2A)
        except Exception:
            pass
    try:
        e.add_peer(BCAST)
    except Exception:
        pass
    try:
        sta.config(txpower=TX_POWER_DBM)
    except Exception as ex:
        print('txpower set failed:', ex)
    led = Pin(LED, Pin.OUT, value=1 - LED_ON)
    adc = ADC(Pin(ADC_PIN))
    adc.atten(ADC.ATTN_11DB)
    sid = os.urandom(8)
    pkt[0:8] = sid
    for b in range(NB):
        ctrbuf[16 * b:16 * b + 8] = sid
        struct.pack_into('>I', ctrbuf, 16 * b + 12, b)
    ecb = cryptolib.aes(_EK, 1)         # mode 1 = ECB
    pt[2] = 0


# ---------------- per-frame work, split into small steps ----------------
def j_enc():
    global p0, i0
    p0 = enc_st[0]
    i0 = enc_st[1]
    _enc(src, FRAME, adp_mv, enc_st, _STEP, GAIN)


def j_crypt():
    global seq, sid
    if seq >= 0xFFFFFFFF:               # never reuse an IV: new random sid
        sid = os.urandom(8)
        pkt[0:8] = sid
        for b in range(NB):
            ctrbuf[16 * b:16 * b + 8] = sid
        seq = 0
    struct.pack_into('<h', pt, 0, p0)
    pt[2] = i0
    struct.pack_into('>I', pkt, 8, seq)
    for b in range(NB):
        struct.pack_into('>I', ctrbuf, 16 * b + 8, seq)
    seq += 1
    ecb.encrypt(ctrbuf, ksbuf)                          # keystream
    _xor(pt, ksbuf, ct_mv, BODY)                        # ciphertext written straight into the packet


def j_mac1():
    global inner
    h = hashlib.sha256(_IPAD)
    h.update(pkt_mv[:PKT_LEN - TAG])
    inner = h.digest()


def j_mac2():
    o = hashlib.sha256(_OPAD)
    o.update(inner)
    pkt_mv[PKT_LEN - TAG:] = o.digest()[:TAG]


def j_send():
    global npk, send_err, last_err
    try:
        e.send(BCAST, pkt, False)       # async: no ACK on broadcast, a failed frame is just a gap
    except OSError as ex:
        send_err += 1
        last_err = ex.args[0] if ex.args else -1
    npk += 1
    if npk & 15 == 0:
        led.value(LED_ON if (npk >> 4) & 1 else 1 - LED_ON)     # slow blink = sending
    if npk % GC_EVERY == GC_EVERY // 2:
        gc.collect()


def j_stat():
    _mm(src, FRAME, mm_st)


def j_diag():
    # runs in a sample slot once every DIAG_EVERY packets; print() costs a little time, so keep it rare
    global d_t, d_npk
    if npk % DIAG_EVERY:
        return
    now = time.ticks_ms()
    dt = time.ticks_diff(now, d_t)
    n = (npk - d_npk) * FRAME
    if dt <= 0 or n <= 0:
        return
    hw = -1
    try:
        hw = e.stats()[2]               # tx_failures counted by the ESP-NOW send callback
    except Exception:
        pass
    print('TX %ds pkts=%d seq=%d rate=%d/%dHz adc[min=%d max=%d mean=%d] sendErr=%d(last %d) hwFail=%s '
          'jobMax=%dus(j%d) filled=%d.%d%% maxgap=%d free=%d' % (
              time.ticks_diff(now, T0) // 1000, npk, seq, n * 1000 // dt, SAMPLE_RATE,
              mm_st[0], mm_st[1], (mm_st[2] << 4) // n, send_err, last_err, hw,
              dg[0], dg[1], dg[2] * 100 // n, (dg[2] * 1000 // n) % 10, dg[3], gc.mem_free()))
    mm_st[0] = 65535
    mm_st[1] = 0
    mm_st[2] = 0
    dg[0] = 0
    dg[2] = 0
    dg[3] = 0
    d_t = now
    d_npk = npk


JOBS = (j_enc, j_crypt, j_mac1, j_mac2, j_send, j_stat, j_diag)


# ---------------- rate selection ----------------
def set_rate(r):
    global SAMPLE_RATE, RATE_IDX, DIAG_EVERY
    SAMPLE_RATE = r
    RATE_IDX = RATES.index(r)
    pt[3] = RATE_IDX
    DIAG_EVERY = max(1, r * DIAG_S // FRAME)


def calibrate():
    # Measure what the sampler really costs on THIS board: the ADC read, the loop around it, and each
    # per-frame job.  Jobs stall sampling; the missed slots are interpolated, so the number to keep small
    # is (job time) / (frame time).
    global src, npk, seq
    rd = adc.read_u16
    tus = time.ticks_us
    tdf = time.ticks_diff
    for _ in range(20):
        rd()
    t = tus()
    for _ in range(300):
        rd()
    t_read = tdf(tus(), t) / 300
    buf = bufA
    nxt = tus()
    acc = 0
    i = 0
    pv = 0
    si = 1 << 30
    per_us = 100
    t = tus()
    for _ in range(300):                # same statements as the sampler loop, but never waiting
        t0 = tus()
        v = rd()
        d = (t0 - nxt) & MASK
        if d >= per_us:
            pv = v
        buf[i] = v
        i += 1
        acc += 2000
        nxt = (nxt + (acc >> 4)) & MASK
        acc &= 15
        pv = v
        if i >= si:
            si = 0
        if i >= FRAME:
            i = 0
    t_loop = tdf(tus(), t) / 300
    src = bufA
    jt = []
    for j in (j_enc, j_crypt, j_mac1, j_mac2, j_send, j_stat):
        t = tus()
        j()
        jt.append(tdf(tus(), t))
    jobs_total = sum(jt)
    enc_st[0] = enc_st[1] = enc_st[2] = 0
    mm_st[0] = 65535
    mm_st[1] = mm_st[2] = 0
    npk = 0
    best = None
    for r in sorted(RATES, reverse=True):
        period = 1000000 / r
        if period >= t_loop * AUTO_MARGIN and jobs_total / (FRAME * period) <= MAX_GAP_FRAC:
            best = r
            break
    print('calibration: adc read %.0f us, sampler loop %.0f us/sample, jobs enc/crypt/mac1/mac2/send/stat = %s us'
          % (t_read, t_loop, jt))
    print('  jobs %d us per %d-sample frame -> highest rate with loop headroom and <= %d%% interpolated: %s Hz'
          % (jobs_total, FRAME, int(MAX_GAP_FRAC * 100), best))
    if SAMPLE_RATE:
        if best is None or SAMPLE_RATE > best:
            print('  WARNING: forced %d Hz is above what this board sustains cleanly' % SAMPLE_RATE)
        set_rate(SAMPLE_RATE)
    else:
        set_rate(best if best else min(RATES))
    print('  using %d Hz (%.1f%% of slots will be interpolated)' % (
        SAMPLE_RATE, 100.0 * jobs_total * SAMPLE_RATE / (FRAME * 1000000)))


# ---------------- sampler ----------------
# Fixed time grid: slot k is due at t0 + k * period.  If something stalls the loop (a job, GC, a print) the
# slots that were missed are filled by linear interpolation between the last real sample and the one just
# read, so the stream keeps the right length and pitch and no sample is ever read "early".
BIG = 1 << 30
NJ = len(JOBS)
SPACE = FRAME // (NJ + 1)
SCHED = [1 + j * SPACE for j in range(NJ)] + [BIG]     # sample index (within the frame) at which each job runs


def run():
    global src, d_t
    rd = adc.read_u16
    tus = time.ticks_us
    nj = NJ
    enc_st[0] = enc_st[1] = 0
    mm_st[0] = 65535
    mm_st[1] = mm_st[2] = 0

    acc = 0
    for _ in range(64):                 # seed the DC estimate so there is no start-up step
        acc += rd()
    enc_st[2] = (acc >> 6) << 10

    per16 = (1000000 * 16) // SAMPLE_RATE      # sample period in 1/16 us (exact for 8000 Hz = 125 us)
    per_us = per16 >> 4
    maxfill = FRAME                     # a stall longer than one frame: give up the grid and re-sync
    acc = 0
    cur = bufA
    i = 0
    job = nj                            # nothing to process until the first frame is complete
    si = BIG
    pv = rd()
    nxt = tus()
    d_t = time.ticks_ms()

    while True:
        t = tus()
        while ((t - nxt) & MASK) >= HALF:       # wait until the slot is due (plain int maths: no calls)
            t = tus()
        v = rd()
        d = (t - nxt) & MASK                    # how late we are, us
        if d < per_us:
            cur[i] = v
            i += 1
            acc += per16
            nxt = (nxt + (acc >> 4)) & MASK
            acc &= 15
            if i >= FRAME:
                src = cur
                cur = bufB if cur is bufA else bufA
                i = 0
                job = 0
                si = SCHED[0]
        else:                                   # missed m slots: interpolate them, then store the real sample
            m = d // per_us
            resync = False
            if m > maxfill:
                m = maxfill
                resync = True
            dg[2] += m
            if m > dg[3]:
                dg[3] = m
            k = 0
            while k <= m:
                if k < m:
                    cur[i] = pv + ((v - pv) * (k + 1)) // (m + 1)
                else:
                    cur[i] = v
                i += 1
                if i >= FRAME:
                    src = cur
                    cur = bufB if cur is bufA else bufA
                    i = 0
                    job = 0
                    si = SCHED[0]
                k += 1
            acc += per16 * (m + 1)
            nxt = (nxt + (acc >> 4)) & MASK
            acc &= 15
            if resync:
                nxt = tus()
        pv = v
        if i >= si:
            t_a = tus()
            JOBS[job]()
            d = (tus() - t_a) & MASK
            if d > dg[0]:
                dg[0] = d
                dg[1] = job
            job += 1
            si = SCHED[job]


T0 = time.ticks_ms()


def banner():
    try:
        mac = ''.join('%02x' % b for b in sta.config('mac'))
    except Exception:
        mac = '?'
    try:
        pw = sta.config('txpower')
    except Exception:
        pw = '?'
    try:
        ch = sta.config('channel')
    except Exception:
        ch = '?'
    print('--- ADC audio TX ---')
    print('mac=%s channel=%s (cfg %d) txpower=%s dBm (cfg %d) lr=%s' % (mac, ch, CHANNEL, pw, TX_POWER_DBM, LONG_RANGE))
    print('adc pin %d, %d Hz, %d samples/pkt, %d bytes/pkt, %d pkts/s, gain x%.2f, sid=%s' % (
        ADC_PIN, SAMPLE_RATE, FRAME, PKT_LEN, SAMPLE_RATE // FRAME, GAIN / 16, sid.hex()))


def main():
    setup()
    gc.collect()
    calibrate()
    gc.collect()
    banner()
    run()


if __name__ == "__main__":
    main()
