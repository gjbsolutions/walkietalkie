# adc_audio_rx.py -- ESP-NOW encrypted audio RECEIVER / USB bridge, ESP32-C3, MicroPython. Save as main.py
#
# ESP-NOW broadcast -> verify HMAC -> AES-256-CTR decrypt -> IMA-ADPCM decode -> 16-bit PCM
# -> USB serial frames that viewer_audio.html understands (Web Serial on desktop, WebUSB on Android).
#
# Pair it with adc_audio_tx.py (same KEY_HEX, CHANNEL, LONG_RANGE).  Plug this board into the PC with the
# C3's native USB port, open viewer_audio.html in Chrome/Edge and press Connect.
#
# USB stream (what the viewer parses):  AA 55 type n_lo n_hi payload
#   type 1 DATA : seq u16 LE | fmt u8 (rate index in bits 0-3, 16-bit signed) | PCM int16 LE
#   type 2 STATS: rssi i8 | forwarded u32 | drops u32 | uptime_s u32 | usb_fails u16   (15 bytes)
# Do not print() anything while running: it would be mixed into the audio stream (the viewer shows it in
# its "Device console" box, but it costs time).

import sys
import time
import array
import struct
import hashlib
import micropython
import network
import espnow
import cryptolib
from machine import Pin

# ======================= CONFIG =======================
KEY_HEX = "f803703aa2d6b3bdd660e3c095f2a4e95a11b6bcf87cda30f10d90cae8a158ab"   # same as the sender
CHANNEL = 1
LONG_RANGE = False      # same as the sender
LED = 8
LED_ON = 0              # 0 = active-low LED (SuperMini)
STATS_MS = 500
# ======================================================

KEY = bytes.fromhex(KEY_HEX)
if len(KEY) != 32 or KEY == bytes(32):
    raise ValueError("Set KEY_HEX to the sender's 32-byte key (64 hex chars)")

HDR = 12
TAG = 8
MIN_LEN = HDR + 4 + 1 + TAG
NRATES = 8                                  # len(RATES) in viewer_audio.html
MAX_SAMPLES = 2 * (250 - HDR - 4 - TAG)

# ---------------- crypto ----------------
_EK = hashlib.sha256(KEY + b'walkie-enc').digest()
_MK = hashlib.sha256(KEY + b'walkie-mac').digest()
_IPAD = bytes([b ^ 0x36 for b in _MK] + [0x36] * 32)
_OPAD = bytes([b ^ 0x5C for b in _MK] + [0x5C] * 32)


def _tag(data):
    h = hashlib.sha256(_IPAD)
    h.update(data)
    o = hashlib.sha256(_OPAD)
    o.update(h.digest())
    return o.digest()[:TAG]


_ecb = cryptolib.aes(_EK, 1)                # mode 1 = ECB (this MicroPython build has no CTR mode)


def _ctr(hdr, data):
    # CTR built on ECB: counter block i = sid | seq | i (u32 BE); keystream XOR data
    n = len(data)
    nb = (n + 15) // 16
    cb = bytearray(nb * 16)
    for b in range(nb):
        cb[16 * b:16 * b + 12] = hdr
        struct.pack_into('>I', cb, 16 * b + 12, b)
    ks = _ecb.encrypt(cb)
    out = bytearray(n)
    _xor(data, ks, out, n)
    return out


# ---------------- IMA ADPCM decoder ----------------
_STEP = array.array('H', [
    7, 8, 9, 10, 11, 12, 13, 14, 16, 17, 19, 21, 23, 25, 28, 31, 34, 37, 41, 45, 50, 55, 60, 66,
    73, 80, 88, 97, 107, 118, 130, 143, 157, 173, 190, 209, 230, 253, 279, 307, 337, 371, 408,
    449, 494, 544, 598, 658, 724, 796, 876, 963, 1060, 1166, 1282, 1411, 1552, 1707, 1878, 2066,
    2272, 2499, 2749, 3024, 3327, 3660, 4026, 4428, 4871, 5358, 5894, 6484, 7132, 7845, 8630,
    9493, 10442, 11487, 12635, 13899, 15289, 16818, 18500, 20350, 22385, 24623, 27086, 29794,
    32767])


@micropython.viper
def _dec(inp, n: int, out, st, tbl) -> int:
    # inp: n/2 bytes. out: n int16 samples. st: int32[2] = [pred, index]
    b = ptr8(inp)
    o = ptr16(out)
    t = ptr32(st)
    stp = ptr16(tbl)
    pred = int(t[0])
    idx = int(t[1])
    i = 0
    while i < n:
        v = int(b[i >> 1])
        if i & 1:
            code = v >> 4
        else:
            code = v & 15
        step = int(stp[idx])
        diff = step >> 3
        if code & 4:
            diff += step
        if code & 2:
            diff += step >> 1
        if code & 1:
            diff += step >> 2
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
        o[i] = pred
        i += 1
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


# ---------------- state ----------------
e = led = None
dec_st = array.array('i', [0, 0])
frame = bytearray(8 + 2 * MAX_SAMPLES)      # USB header (8) + PCM, decoded in place
frame_mv = memoryview(frame)
pcm_mv = frame_mv[8:]
seen = {}                                   # sid -> highest seq accepted (replay protection), max 8 senders
out = sys.stdout.buffer
fwd = drops = usbfail = 0
cur_sid = None
last_seq = 0
ucnt = 0                                    # continuous 16-bit sequence number shown to the viewer


def setup():
    global e, led
    sta = network.WLAN(network.STA_IF)
    sta.active(True)
    try:
        if LONG_RANGE:
            sta.config(protocol=network.MODE_11B | network.MODE_11G |
                                network.MODE_11N | network.MODE_LR)
        sta.config(channel=CHANNEL)
    except Exception:
        pass
    e = espnow.ESPNow()
    e.config(rxbuf=4096)
    e.active(True)
    if LONG_RANGE:
        try:
            e.config(rate=0x2A)
        except Exception:
            pass
    led = Pin(LED, Pin.OUT, value=1 - LED_ON)


def open_pkt(m):
    # -> (sid, seq, pred, idx, rate_idx, adpcm bytes) or None
    n = len(m)
    if n < MIN_LEN or n > 250:
        return None
    mv = memoryview(m)
    if _tag(mv[:n - TAG]) != bytes(mv[n - TAG:]):
        return None                         # wrong key or tampered
    s = bytes(mv[:8])
    q = struct.unpack('>I', mv[8:12])[0]
    last = seen.get(s)
    if last is not None and q <= last:
        return None                         # replayed or late
    pt = _ctr(bytes(mv[:HDR]), mv[HDR:n - TAG])
    idx = pt[2]
    ridx = pt[3]
    if idx > 88 or ridx >= NRATES:
        return None
    if last is None and len(seen) >= 8:
        del seen[next(iter(seen))]
    seen[s] = q
    return s, q, struct.unpack_from('<h', pt, 0)[0], idx, ridx, memoryview(pt)[4:]


def forward(r):
    global fwd, usbfail, cur_sid, last_seq, ucnt
    s, q, pred, idx, ridx, adp = r
    if s != cur_sid:                        # new sender / sender rebooted: no gap to report
        cur_sid = s
        ucnt = (ucnt + 1) & 0xFFFF
    else:
        gap = q - last_seq - 1
        ucnt = (ucnt + 1 + (gap if gap < 250 else 250)) & 0xFFFF   # >200 makes the viewer re-sync
    last_seq = q
    ns = len(adp) * 2
    dec_st[0] = pred
    dec_st[1] = idx
    _dec(adp, ns, pcm_mv, dec_st, _STEP)
    total = 8 + 2 * ns
    struct.pack_into('<BBBHHB', frame, 0, 0xAA, 0x55, 1, 3 + 2 * ns, ucnt, ridx)
    try:
        w = out.write(frame_mv[:total])
        if w is not None and w < total:
            usbfail += 1
    except OSError:
        usbfail += 1
    fwd += 1


def send_stats(rssi, up_s):
    global usbfail
    try:
        d = drops
        try:
            d += e.stats()[4]               # packets dropped because the ESP-NOW rx buffer was full
        except Exception:
            pass
        out.write(struct.pack('<BBBHbIIIH', 0xAA, 0x55, 2, 15, rssi, fwd, d, up_s, usbfail & 0xFFFF))
    except OSError:
        usbfail += 1


def main():
    global drops
    setup()
    t0 = time.ticks_ms()
    t_stat = t0
    rssi = -128
    nled = 0
    while True:
        mac, msg = e.irecv(20)
        if msg:
            r = open_pkt(msg)
            if r is None:
                drops += 1                  # bad tag (wrong key / corrupted), replay or malformed
            else:
                forward(r)
                try:
                    rssi = e.peers_table[bytes(mac)][0]
                except Exception:
                    pass
                nled += 1
                if nled & 15 == 0:
                    led.value(LED_ON if (nled >> 4) & 1 else 1 - LED_ON)
        now = time.ticks_ms()
        if time.ticks_diff(now, t_stat) >= STATS_MS:
            t_stat = now
            send_stats(rssi, time.ticks_diff(now, t0) // 1000)


if __name__ == "__main__":
    main()
