# -*- coding: utf-8 -*-
"""
BSV IP-to-IP Negotiated Notes
Implementation (single-file) using bitsv + ecdsa.

Requirements:
    pip install bitsv ecdsa

Placeholders: set WIFs via environment variables or edit constants.
This file is intended to be runnable as-is (adjust WIFs / network as needed).
"""

import os
import json
import hmac
import math
import hashlib
import random
import binascii
from dataclasses import dataclass, asdict
from typing import List, Tuple, Dict, Optional

from ecdsa import SECP256k1, SigningKey, ellipticcurve

from bitsv import Key
from bitsv.network import NetworkAPI
from bitsv import base58
from bitsv.utils import hex_to_bytes, bytes_to_hex

# Elliptic curve constants
SECP = SECP256k1
G: ellipticcurve.Point = SECP.generator
N = SECP.order

# ------------------------------
# Canonical JSON, signatures, NoteID
# ------------------------------
import unicodedata

def canonical_json(obj) -> bytes:
    """
    Canonical JSON serializer as specified:
    - UTF-8, NFC normalization for strings
    - keys lexicographically sorted by Unicode code point
    - no insignificant whitespace
    - integers with no leading zeros
    - byte-containing fields expected to be hex strings etc (the caller controls types)
    Returns bytes (utf-8).
    Note: This implementation supports objects built from Python primitives (dict/list/str/int/bool/None).
    """
    def norm_str(s: str) -> str:
        return unicodedata.normalize("NFC", s)

    def encode(value):
        if value is None:
            return "null"
        if isinstance(value, bool):
            return "true" if value else "false"
        if isinstance(value, int):
            # integers as base-10 no leading zeros
            return str(value)
        if isinstance(value, str):
            # ensure NFC and JSON string escaping minimal
            s = norm_str(value)
            # we must escape according to JSON rules (use json encoder for string part only)
            return json.dumps(s, ensure_ascii=False, separators=(",", ":"))
        if isinstance(value, list):
            return "[" + ",".join(encode(v) for v in value) + "]"
        if isinstance(value, dict):
            # keys must be strings; sort by Unicode codepoint
            items = []
            for k in sorted(value.keys(), key=lambda x: [ord(ch) for ch in str(x)]):
                if not isinstance(k, str):
                    raise TypeError("JSON object keys must be strings for canonical_json")
                items.append(json.dumps(k, ensure_ascii=False, separators=(",", ":")) + ":" + encode(value[k]))
            return "{" + ",".join(items) + "}"
        raise TypeError(f"Unsupported type for canonical_json: {type(value)}")

    s = encode(obj)
    return s.encode("utf-8")

def sign_canonical(obj: Dict, signing_key_priv_int: int) -> str:
    """
    Sign canonical_json(obj_without_sig_fields) with ECDSA (secp256k1, sha256).
    Returns hex signature (DER).
    signing_key_priv_int: integer secret exponent (same domain as bitsv/ecdsa usage)
    """
    preimage = canonical_json(obj)
    sk = SigningKey.from_secret_exponent(signing_key_priv_int, curve=SECP)
    sig = sk.sign_digest(sha256(preimage))
    return binascii.hexlify(sig).decode()

def verify_sig_canonical(obj: Dict, signature_hex: str, pubkey_compressed_hex: str) -> bool:
    """
    Verify signature_hex (DER) against canonical_json(obj) using compressed pubkey hex (serP).
    """
    vk_bytes = binascii.unhexlify(pubkey_compressed_hex)
    try:
        vk_point = bytes_to_point(vk_bytes)
    except Exception:
        return False
    vk = SigningKey.from_secret_exponent(1, curve=SECP).get_verifying_key()  # placeholder to get class
    # construct ecdsa.VerifyingKey from compressed point:
    from ecdsa import VerifyingKey
    vk = VerifyingKey.from_string(vk_bytes, curve=SECP)  # ecdsa accepts compressed string here
    preimage = canonical_json(obj)
    sig = binascii.unhexlify(signature_hex)
    try:
        return vk.verify_digest(sig, dbl_sha256(preimage))
    except Exception:
        return False

def le32(i: int) -> bytes:
    return (i & 0xffffffff).to_bytes(4, "little")

def note_id(H_I: bytes, i: int) -> bytes:
    return sha256(H_I + le32(i))


def derive_scalar_spec(Z: bytes, H_I: bytes, label: bytes, i: int, max_ctr=8) -> Tuple[int,int]:
    # label is b"recv" or b"snd"
    def h(pre):
        return hashlib.sha256(pre).digest()
    base = Z + H_I + label + le32(i)
    t = int_from_bytes(h(base)) % N
    ctr = 0
    while t == 0:
        ctr += 1
        if ctr > max_ctr:
            raise ValueError("derive_scalar: counter exhausted")
        t = int_from_bytes(h(base + le32(ctr))) % N
    return t, ctr

def next_u64(seed: bytes, ctr: int) -> Tuple[int,int]:
    r = hashlib.sha256(seed + le32(ctr)).digest()
    u = int.from_bytes(r[:8], "big")
    return u, ctr+1

def draw_uniform(seed: bytes, counter: int, rng: int):
    # returns (value, new_counter)
    M = 1 << 64
    lim = (M // rng) * rng
    while True:
        u, counter = next_u64(seed, counter)
        if u < lim:
            return (u % rng), counter

def estimate_size_bytes(m_inputs: int, n_outputs: int) -> int:
    return 10 + 148 * m_inputs + 34 * n_outputs

def fee_from_feerate(feerate_floor: int, m_inputs: int, n_outputs: int) -> int:
    size = estimate_size_bytes(m_inputs, n_outputs)
    return math.ceil(feerate_floor * size)


# ------------------------------
# §9: Broadcast / pacing / schedule / manager / logging helpers
# ------------------------------
import pathlib
from datetime import datetime, timezone, timedelta
import math

# ---------- Helpers: deterministic H-based PRNG (reused for split & pace) ----------
def next_u64(seed: bytes, ctr: int) -> Tuple[int, int]:
    r = sha256(seed + le32(ctr))
    u = int.from_bytes(r[:8], "big")
    return u, ctr + 1

def draw_uniform(seed: bytes, ctr: int, rng: int) -> Tuple[int, int]:
    if rng <= 0:
        raise ValueError("rng must be >= 1")
    M = 1 << 64
    lim = (M // rng) * rng
    while True:
        u, ctr = next_u64(seed, ctr)
        if u < lim:
            return (u % rng), ctr

# ---------- Validate invoice overrides are within policy bounds ----------
def validate_broadcast_overrides(policy_broadcast: Dict, overrides: Optional[Dict]) -> Dict:
    """
    Returns effective broadcast params (policy overridden by invoice overrides)
    or raises ValueError if overrides violate policy.
    """
    eff = dict(policy_broadcast or {})
    if not overrides:
        return eff
    # simple fields list
    # NOTE: assume canonical JSON validated earlier; here only numeric/bounds checks
    if "strategy" in overrides:
        if overrides["strategy"] not in ("paced", "all_at_once", "bursts"):
            raise ValueError("invalid override strategy")
        if overrides["strategy"] not in (eff.get("strategy_default"), "paced", "all_at_once", "bursts") and eff.get("authority","either") == "either":
            # policy may allow multiple strategies; for simplicity we require it to match default or be permitted
            pass
        eff["strategy_default"] = overrides["strategy"]
    if "min_spacing_ms" in overrides:
        if overrides["min_spacing_ms"] > eff.get("max_spacing_ms", overrides.get("max_spacing_ms", 0)):
            # can't have min > policy max
            raise ValueError("override min_spacing_ms > policy max_spacing_ms")
        eff["min_spacing_ms"] = overrides["min_spacing_ms"]
    if "max_spacing_ms" in overrides:
        if overrides["max_spacing_ms"] < eff.get("min_spacing_ms", overrides.get("min_spacing_ms", 0)):
            raise ValueError("override max_spacing_ms < min_spacing_ms")
        if eff.get("max_spacing_ms") and overrides["max_spacing_ms"] > eff.get("max_spacing_ms"):
            # policy max must be >= override max
            if overrides["max_spacing_ms"] > eff.get("max_spacing_ms"):
                raise ValueError("override max_spacing_ms > policy.max_spacing_ms")
        eff["max_spacing_ms"] = overrides["max_spacing_ms"]
    if "burst_size" in overrides:
        if overrides["burst_size"] > eff.get("burst_size", overrides["burst_size"]):
            raise ValueError("override burst_size > policy.burst_size")
        eff["burst_size"] = overrides["burst_size"]
    if "burst_gap_ms" in overrides:
        if overrides["burst_gap_ms"] > eff.get("burst_gap_ms", overrides["burst_gap_ms"]):
            raise ValueError("override burst_gap_ms > policy.burst_gap_ms")
        eff["burst_gap_ms"] = overrides["burst_gap_ms"]
    if "window_start" in overrides:
        eff["window_start"] = overrides["window_start"]
    if "window_end" in overrides:
        eff["window_end"] = overrides["window_end"]
    if "confirm_depth" in overrides:
        if overrides["confirm_depth"] < eff.get("confirm_depth", 0):
            raise ValueError("override confirm_depth < policy.confirm_depth")
        eff["confirm_depth"] = overrides["confirm_depth"]
    # final temporal check
    if eff.get("window_start") and eff.get("window_end"):
        ws = eff["window_start"]
        we = eff["window_end"]
        try:
            if ws and we:
                tws = datetime.fromisoformat(ws.replace("Z","+00:00"))
                twe = datetime.fromisoformat(we.replace("Z","+00:00"))
                if tws >= twe:
                    raise ValueError("window_start >= window_end")
        except Exception:
            raise ValueError("invalid window timestamps")
    return eff

# ---------- Deterministic schedule builder (§9.5) ----------
def compute_schedule(Z: bytes, H_I: bytes, N: int, policy_broadcast: Dict, invoice_overrides: Optional[Dict], now_ts: float = None) -> List[float]:
    """
    Returns a list of scheduled timestamps (seconds since epoch) for N indices 0..N-1.
    Uses seed S_pace := H(Z || H_I || b"pace") and deterministic draws per spec.
    """
    if now_ts is None:
        now_ts = datetime.now(timezone.utc).timestamp()
    eff = validate_broadcast_overrides(policy_broadcast, invoice_overrides)
    strategy = eff.get("strategy_default", "paced")
    min_spacing = int(eff.get("min_spacing_ms", 0))
    max_spacing = int(eff.get("max_spacing_ms", min_spacing))
    burst_size = int(eff.get("burst_size", 1))
    burst_gap = int(eff.get("burst_gap_ms", 0))
    ws_iso = eff.get("window_start", "")
    we_iso = eff.get("window_end", "")

    def parse_window(w):
        if not w:
            return now_ts
        return datetime.fromisoformat(w.replace("Z","+00:00")).timestamp()

    ws = parse_window(ws_iso)
    we = None
    if we_iso:
        we = parse_window(we_iso)

    seed = sha256(Z + H_I + b"pace")
    ctr = 0
    schedule = []

    if strategy == "all_at_once":
        base = max(now_ts, ws)
        schedule = [base for _ in range(N)]
        return schedule

    if strategy == "paced":
        prev = max(now_ts, ws)
        schedule.append(prev)
        for i in range(1, N):
            rng = max_spacing - min_spacing + 1
            if rng <= 0:
                delta_ms = min_spacing
            else:
                r, ctr = draw_uniform(seed, ctr, rng)
                delta_ms = min_spacing + r
            prev = prev + (delta_ms / 1000.0)
            if we is not None and prev > we:
                prev = we
            schedule.append(prev)
        return schedule

    if strategy == "bursts":
        base = max(now_ts, ws)
        batch_time = base
        idx = 0
        # for deterministic intra-batch offsets use same seed stream
        while idx < N:
            for j in range(burst_size):
                if idx >= N:
                    break
                # epsilon in [0, min_spacing_ms]
                rng = min_spacing + 1
                if rng <= 0:
                    eps_ms = 0
                else:
                    e, ctr = draw_uniform(seed, ctr, rng)
                    eps_ms = e
                t = batch_time + (eps_ms / 1000.0)
                if we is not None and t > we:
                    t = we
                schedule.append(t)
                idx += 1
            batch_time = batch_time + (burst_gap / 1000.0)
        return schedule

    # fallback
    base = max(now_ts, ws)
    return [base for _ in range(N)]

# ---------- Simple persistent store (NoteMeta + append-only logs) ----------
class SimpleStore:
    """
    Minimal JSON-backed store for NoteMeta entries and audit log.
    - directory: path to folder to keep files per-invoice
    - NoteMeta saved in notes.json (dict index -> meta)
    - log saved in events.log (newline-delimited canonical JSON)
    """
    def __init__(self, directory: str):
        self.dir = pathlib.Path(directory)
        self.dir.mkdir(parents=True, exist_ok=True)
        self.notes_file = self.dir / "notes.json"
        self.log_file = self.dir / "events.log"
        if not self.notes_file.exists():
            self.notes_file.write_text(json.dumps({}))
        if not self.log_file.exists():
            self.log_file.write_text("")

    def _load_notes(self) -> Dict[int, Dict]:
        s = self.notes_file.read_text()
        return {int(k): v for k, v in json.loads(s).items()} if s else {}

    def _save_notes(self, notes: Dict[int, Dict]):
        # canonical json with sorted keys
        out = {str(k): notes[k] for k in sorted(notes.keys())}
        self.notes_file.write_text(json.dumps(out, ensure_ascii=False, separators=(",", ":"), sort_keys=True))

    def list_note_metas(self) -> List[Dict]:
        notes = self._load_notes()
        return [notes[k] for k in sorted(notes.keys())]

    def get(self, i: int) -> Optional[Dict]:
        notes = self._load_notes()
        return notes.get(i)

    def set_note_meta(self, i: int, meta: Dict):
        notes = self._load_notes()
        notes[i] = meta
        self._save_notes(notes)

    def update(self, meta: Dict):
        i = meta["i"]
        self.set_note_meta(i, meta)

    def current_version(self, i: int) -> int:
        m = self.get(i)
        return m.get("version", 1) if m else 0

    def get_tx_hex(self, i: int) -> Optional[str]:
        m = self.get(i)
        return m.get("tx_hex") if m else None

    def append_event(self, obj: Dict):
        # write canonical JSON line
        s = json.dumps(obj, ensure_ascii=False, separators=(",", ":"), sort_keys=True)
        with open(self.log_file, "a", encoding="utf-8") as f:
            f.write(s + "\n")

# ---------- append log helper (signed) ----------
def append_log_event(store: SimpleStore, event_obj: Dict, signer_priv_int: Optional[int] = None):
    # timestamp
    event_obj = dict(event_obj)
    event_obj.setdefault("at", datetime.now(timezone.utc).isoformat())
    if signer_priv_int:
        try:
            # sign canonical bytes of event (sig field omitted)
            to_sign = dict(event_obj)
            # do not include sig fields if present
            to_sign.pop("sig", None)
            sig = sign_canonical(to_sign, signer_priv_int)
            event_obj["sig"] = sig
            # include sig_key for verifier convenience
            event_obj["sig_key"] = binascii.hexlify(priv_to_pub_compressed(signer_priv_int)).decode()
            event_obj["sig_alg"] = "secp256k1-sha256"
        except Exception:
            pass
    store.append_event(event_obj)

# ---------- Broadcast manager (state machine tick) ----------
class BroadcastManager:
    def __init__(self, engine: "NegotiatedNotes", store: SimpleStore, network_name: str = "main"):
        self.engine = engine
        self.store = store
        # NetworkAPI instance (bitsv). If issues arise adapt to bitsv version.
        try:
            self.net = NetworkAPI(network_name)
        except Exception:
            # fallback to module NetworkAPI
            self.net = NetworkAPI
        # params
        self.policy_broadcast = {}  # should be filled from payee policy
        self.invoice_overrides = None

    def load_policy(self, policy_broadcast: Dict, invoice_overrides: Optional[Dict] = None):
        # store broadcast policy & overrides
        self.policy_broadcast = policy_broadcast or {}
        self.invoice_overrides = invoice_overrides

    def tick(self):
        """
        Single scheduler pass. Should be called periodically by host.
        Applies:
         - scheduled broadcasts for queued notes
         - rebroadcast per rebroadcast_interval_s
         - hold_time_max_s -> reissue or cancel
         - confirmation checks -> mark confirmed
        """
        now_ts = datetime.now(timezone.utc).timestamp()
        metas = self.store.list_note_metas()
        for meta in metas:
            try:
                status = meta.get("status", "constructed")
                i = meta["i"]
                current_version = self.store.current_version(i)
                # ignore obsolete older versions
                if meta.get("version", 1) < current_version:
                    # ensure older version is marked obsolete
                    if meta.get("status") != "obsolete":
                        meta["status"] = "obsolete"
                        self.store.update(meta)
                    continue

                # handle queued -> scheduled broadcast
                if status in ("signed", "queued"):
                    scheduled_at = meta.get("scheduled_at_ts", None)
                    if scheduled_at is None:
                        # if no schedule, treat as immediate candidate
                        scheduled_at = now_ts
                        meta["scheduled_at_ts"] = scheduled_at
                        meta["scheduled_at"] = datetime.fromtimestamp(scheduled_at, timezone.utc).isoformat()
                        self.store.update(meta)

                    if now_ts >= scheduled_at:
                        # broadcast if not yet broadcasted and version is current
                        if meta.get("status") in ("signed", "queued"):
                            tx_hex = meta.get("tx_hex")
                            if not tx_hex:
                                continue
                            try:
                                self.net.broadcast_tx(tx_hex)
                                meta["broadcast_at"] = datetime.now(timezone.utc).isoformat()
                                meta["broadcast_at_ts"] = datetime.now(timezone.utc).timestamp()
                                meta["status"] = "broadcast"
                                meta["last_rebroadcast_at_ts"] = meta["broadcast_at_ts"]
                                self.store.update(meta)
                                # log event
                                evt = {"event": "broadcast", "invoice_hash": binascii.hexlify(self.engine.H_I).decode(), "i": i, "txid": meta.get("txid",""), "by": binascii.hexlify(self.engine.payer.identity.vk_compressed()).decode()}
                                append_log_event(self.store, evt, signer_priv_int=self.engine.payer.identity.priv)
                            except Exception as e:
                                # move on and keep it queued/signed for next tick
                                meta.setdefault("errors", []).append(str(e))
                                self.store.update(meta)

                # handle broadcast/seen -> check confirmations & rebroadcast rules
                if status in ("broadcast", "seen"):
                    txid = meta.get("txid")
                    # Try to fetch confirmations via payer.key (bitsv)
                    conf = None
                    try:
                        # bitsv Key has get_transaction or NetworkAPI can provide; try both safely
                        if hasattr(self.engine.payer.key, "get_transaction"):
                            txinfo = self.engine.payer.key.get_transaction(txid)
                            conf = getattr(txinfo, "confirmations", None)
                        else:
                            # fallback: no confirmation info
                            conf = None
                    except Exception:
                        conf = None

                    effective_d = meta.get("confirm_depth", self.policy_broadcast.get("confirm_depth", 1))
                    if conf is not None and conf >= effective_d:
                        meta["status"] = "confirmed"
                        meta["confirmed_at"] = datetime.now(timezone.utc).isoformat()
                        self.store.update(meta)
                        evt = {"event": "confirmed", "invoice_hash": binascii.hexlify(self.engine.H_I).decode(), "i": i, "txid": txid, "confirmations": conf}
                        append_log_event(self.store, evt, signer_priv_int=self.engine.payer.identity.priv)
                        continue

                    # rebroadcast policy
                    last_rb = meta.get("last_rebroadcast_at_ts", meta.get("broadcast_at_ts", 0))
                    reb_int = meta.get("rebroadcast_interval_s", self.policy_broadcast.get("rebroadcast_interval_s", 600))
                    if now_ts - last_rb >= max(60, reb_int):
                        try:
                            tx_hex = meta.get("tx_hex")
                            if tx_hex:
                                self.net.broadcast_tx(tx_hex)
                                meta["last_rebroadcast_at_ts"] = now_ts
                                meta["last_rebroadcast_at"] = datetime.now(timezone.utc).isoformat()
                                self.store.update(meta)
                                append_log_event(self.store, {"event":"rebroadcast","i":i,"txid":meta.get("txid","")}, signer_priv_int=self.engine.payer.identity.priv)
                        except Exception as e:
                            meta.setdefault("errors",[]).append(str(e))
                            self.store.update(meta)

                # hold-time enforcement for queued/signed
                if status in ("signed", "queued"):
                    created_at_ts = meta.get("created_at_ts", now_ts)
                    hold_max = meta.get("hold_time_max_s", self.policy_broadcast.get("hold_time_max_s", 0))
                    if hold_max and (now_ts - created_at_ts) >= hold_max:
                        # normative: choose exactly one (reissue preferred)
                        # call reissue
                        try:
                            self.reissue_note(i, reason="hold_timeout")
                        except Exception:
                            # fallback: cancel
                            self.cancel_note(i, reason="hold_timeout")
            except Exception:
                # swallow per-note errors to avoid tick crash; they are logged in store
                continue

    def broadcast_now(self, i: int):
        meta = self.store.get(i)
        if not meta:
            raise ValueError("no note meta")
        if meta.get("version",1) < self.store.current_version(i):
            raise ValueError("version obsolete, refuse broadcast")
        tx_hex = meta.get("tx_hex")
        if not tx_hex:
            raise ValueError("no tx_hex")
        self.net.broadcast_tx(tx_hex)
        meta["broadcast_at"] = datetime.now(timezone.utc).isoformat()
        meta["broadcast_at_ts"] = datetime.now(timezone.utc).timestamp()
        meta["status"] = "broadcast"
        meta["last_rebroadcast_at_ts"] = meta["broadcast_at_ts"]
        self.store.update(meta)
        append_log_event(self.store, {"event":"broadcast_manual","i":i,"txid":meta.get("txid","")}, signer_priv_int=self.engine.payer.identity.priv)

    # ---------- reissue procedure (pre-broadcast) ----------
    def reissue_note(self, i: int, reason: str = "reissue"):
        meta = self.store.get(i)
        if not meta:
            raise ValueError("note not found")
        if meta.get("status") == "confirmed":
            raise ValueError("cannot reissue confirmed note")
        # release old reservation if any (assume reservation metadata present)
        # For this simple implementation we won't interact with an external reservation table
        # Instead we attempt to select new inputs and create new tx
        plans = [NotePlan(index=i, amount=meta["amount"], recv_address=meta["addr"], sender_change_address=meta.get("change_addr"))]
        utxos = fetch_utxos_for_key(self.engine.payer.key)
        # reserve_disjoint_inputs returns list of (sel, change, fee) tuples in order of plans
        try:
            reserved = reserve_disjoint_inputs(utxos, plans, fee_floor=meta.get("feerate_floor", self.policy_broadcast.get("feerate_floor", 1)), dust_limit=meta.get("dust_limit", 546), Z=self.engine.Z, H_I=self.engine.H_I)
        except Exception as e:
            # can't reissue -> mark conflict
            meta["status"] = "conflict"
            meta.setdefault("errors", []).append(str(e))
            self.store.update(meta)
            append_log_event(self.store, {"event":"reissue_failed","i":i,"reason":str(e)}, signer_priv_int=self.engine.payer.identity.priv)
            raise

        sel, change_amt, fee_used = reserved[0]
        # build new tx (signed)
        tx_hex = self.engine.create_signed_note_tx(self.engine.payer.key, sel, meta["amount"], meta["addr"], meta.get("change_addr"), fee_used)
        txid = bytes_to_hex(dbl_sha256(hex_to_bytes(tx_hex))[::-1])
        # mark old raw bytes voided_offchain
        old_txid = meta.get("txid","")
        meta_old = dict(meta)
        meta_old["status"] = "reissued"
        meta_old["voided_offchain"] = True
        self.store.update(meta_old)
        append_log_event(self.store, {"event":"reissued_old","i":i,"txid_old":old_txid}, signer_priv_int=self.engine.payer.identity.priv)
        # new meta
        new_meta = dict(meta)
        new_meta["version"] = meta.get("version", 1) + 1
        new_meta["supersedes"] = old_txid
        new_meta["tx_hex"] = tx_hex
        new_meta["txid"] = txid
        new_meta["status"] = "signed"
        new_meta["created_at"] = datetime.now(timezone.utc).isoformat()
        new_meta["created_at_ts"] = datetime.now(timezone.utc).timestamp()
        new_meta["fee"] = fee_used
        new_meta["change_amount"] = change_amt
        new_meta["inputs"] = [{"txid": u.txid, "vout": u.vout, "value": u.amount} for u in sel]
        self.store.update(new_meta)
        # append reissue event
        evt = {
            "event":"reissue",
            "invoice_hash": binascii.hexlify(self.engine.H_I).decode(),
            "i": i,
            "note_id": binascii.hexlify(note_id(self.engine.H_I, i)).decode(),
            "version": new_meta["version"],
            "supersedes": old_txid,
            "txid_new": txid,
            "fee": fee_used,
            "by": binascii.hexlify(self.engine.payer.identity.vk_compressed()).decode()
        }
        append_log_event(self.store, evt, signer_priv_int=self.engine.payer.identity.priv)

    # ---------- cancellation procedure ----------
    def cancel_note(self, i: int, reason: str = "cancelled"):
        meta = self.store.get(i)
        if not meta:
            raise ValueError("note not found")
        # release reservation (not implemented externally in this simple store)
        meta["status"] = "cancelled"
        meta["cancel_reason"] = reason
        meta["cancelled_at"] = datetime.now(timezone.utc).isoformat()
        self.store.update(meta)
        evt = {
            "event": "cancel",
            "invoice_hash": binascii.hexlify(self.engine.H_I).decode(),
            "i": i,
            "note_id": binascii.hexlify(note_id(self.engine.H_I, i)).decode(),
            "reason": reason,
            "by": binascii.hexlify(self.engine.payer.identity.vk_compressed()).decode()
        }
        append_log_event(self.store, evt, signer_priv_int=self.engine.payer.identity.priv)


# ------------------------------
# §10 Receipts & selective disclosure (leaf, merkle, proofs, manifest)
# ------------------------------
from typing import Any

def encode_le64(i: int) -> bytes:
    return (i & 0xffffffffffffffff).to_bytes(8, "little")

def addr_payload_from_pub_compressed(pub_compressed: bytes) -> bytes:
    """
    addr_payload := version(1 byte = 0x00) || h160(serP(pub))
    """
    h = h160(pub_compressed)  # 20 bytes
    return b"\x00" + h

def receipt_leaf_preimage(i: int, txid_hex: str, amount: int, recv_pub_compressed: bytes) -> bytes:
    """
    Build the exact preimage bytes for leaf i as spec §10.2
    - label "leaf"
    - LE32(i) little-endian 4 bytes
    - txid (32 bytes big-endian) -> bytes.fromhex(txid_hex)
    - amount (8 bytes little-endian)
    - addr_payload (1 + 20 bytes)
    """
    if len(txid_hex) != 64:
        raise ValueError("txid hex must be 64 hex chars (32 bytes)")
    label = b"leaf"
    le_i = le32(i)            # 4 bytes little-endian
    txid_bytes = bytes.fromhex(txid_hex)  # 32 bytes big-endian display order
    amt_bytes = encode_le64(amount)       # 8 bytes little-endian
    addr_payload = addr_payload_from_pub_compressed(recv_pub_compressed)  # 21 bytes
    preimage = label + le_i + txid_bytes + amt_bytes + addr_payload
    return preimage

def receipt_leaf_hash(i: int, txid_hex: str, amount: int, recv_pub_compressed: bytes) -> bytes:
    pre = receipt_leaf_preimage(i, txid_hex, amount, recv_pub_compressed)
    return sha256(pre)

def merkle_root_sha256(leaves: List[bytes]) -> bytes:
    """
    Merkle root using single SHA-256 for parents (spec §10.3).
    Leaves are expected to be 32-byte values (L_i).
    Bitcoin-style padding: duplicate last element if layer odd.
    """
    if not leaves:
        raise ValueError("At least one leaf required")
    level = leaves[:]
    while len(level) > 1:
        if len(level) % 2 == 1:
            level.append(level[-1])
        parents = []
        for j in range(0, len(level), 2):
            parents.append(sha256(level[j] + level[j+1]))
        level = parents
    return level[0]

def merkle_path_sha256(leaves: List[bytes], index: int) -> List[Tuple[bytes, str]]:
    """
    Return list of (sibling_hash, pos) from leaf->root where pos indicates whether the running hash is on the left or right.
    pos = "L" means running hash is left child (so compute SHA256(running || sibling)).
    pos = "R" means running hash is right child (so compute SHA256(sibling || running)).
    """
    if index < 0 or index >= len(leaves):
        raise IndexError("leaf index out of range")
    path = []
    level = leaves[:]
    idx = index
    while len(level) > 1:
        if len(level) % 2 == 1:
            level.append(level[-1])
        pair_index = idx ^ 1
        # determine position: if idx % 2 == 0 then running is left, sibling is right
        pos = "L" if (idx % 2 == 0) else "R"
        sibling = level[pair_index]
        path.append((sibling, pos))
        # build parent level
        next_level = []
        for j in range(0, len(level), 2):
            next_level.append(sha256(level[j] + level[j+1]))
        level = next_level
        idx //= 2
    return path

def build_receipt_manifest(H_I: bytes, note_results: List["NoteResult"], payee_pub_compressed_for_addr: Dict[int, bytes] = None) -> Dict:
    """
    Build minimal manifest:
    {
      "invoice_hash": "<hex H_I>",
      "merkle_root": "<hex M>",
      "count": N,
      "entries": [{"i":, "txid":"<hex 32-byte>"} ...]
    }
    - note_results: list of NoteResult objects (index, txid, amount, recv_address)
    - payee_pub_compressed_for_addr (optional): map index -> recv_pub_compressed (to compute leaves if needed)
    The manifest purposely omits amounts/addresses per spec.
    """
    # order by index ascending
    note_results_sorted = sorted(note_results, key=lambda r: r.index)
    entries = []
    leaves = []
    for r in note_results_sorted:
        entries.append({"i": r.index, "txid": r.txid})
        # if payee public key bytes provided, compute leaf hash; else require later when proving
        if payee_pub_compressed_for_addr and r.index in payee_pub_compressed_for_addr:
            pub = payee_pub_compressed_for_addr[r.index]
            L = receipt_leaf_hash(r.index, r.txid, r.amount, pub)
            leaves.append(L)
        else:
            # placeholder: client can compute leaves later when they have pub key and amount
            leaves.append(None)

    # if all leaves available compute root, else put root as empty placeholder until built
    if all(L is not None for L in leaves):
        root = merkle_root_sha256(leaves)
        root_hex = binascii.hexlify(root).decode()
    else:
        root_hex = "00" * 32

    manifest = {
        "invoice_hash": binascii.hexlify(H_I).decode(),
        "merkle_root": root_hex,
        "count": len(entries),
        "entries": entries
    }
    return manifest

def compute_leaves_from_results_and_pubs(note_results: List["NoteResult"], recv_pub_compressed_map: Dict[int, bytes]) -> List[bytes]:
    """
    Helper: compute L_i list in ascending index order, using recv_pub_compressed_map {index: pub_compressed_bytes}.
    """
    sorted_results = sorted(note_results, key=lambda r: r.index)
    leaves = []
    for r in sorted_results:
        if r.index not in recv_pub_compressed_map:
            raise ValueError(f"missing recipient pub for index {r.index}")
        pub = recv_pub_compressed_map[r.index]
        leaves.append(receipt_leaf_hash(r.index, r.txid, r.amount, pub))
    return leaves

def prove_leaf(note_results: List["NoteResult"], recv_pub_compressed_map: Dict[int, bytes], index: int) -> Dict:
    """
    Build single-leaf proof structure:
    {
      "invoice_hash": "<hex H_I>",
      "merkle_root": "<hex M>",
      "leaf": {"i":, "txid":"...", "amount":, "addr_payload":"<hex 21-byte>"},
      "path": [{"pos": "L"|"R", "hash": "<hex 32-byte>"} ...]
    }
    """
    sorted_results = sorted(note_results, key=lambda r: r.index)
    N = len(sorted_results)
    # map index to position in sorted list (they already should be sorted by index and contiguous)
    positions = {r.index: idx for idx, r in enumerate(sorted_results)}
    if index not in positions:
        raise IndexError("index not present in results")
    pos = positions[index]
    # build leaves
    leaves = compute_leaves_from_results_and_pubs(sorted_results, recv_pub_compressed_map)
    root = merkle_root_sha256(leaves)
    path = merkle_path_sha256(leaves, pos)
    # leaf data fields
    r = next(rr for rr in sorted_results if rr.index == index)
    addr_payload = addr_payload_from_pub_compressed(recv_pub_compressed_map[index])
    proof = {
        "invoice_hash": binascii.hexlify(note_results[0].invoice_hash if hasattr(note_results[0], "invoice_hash") else b"").decode() if note_results else "",
        "merkle_root": binascii.hexlify(root).decode(),
        "leaf": {
            "i": r.index,
            "txid": r.txid,
            "amount": r.amount,
            "addr_payload": binascii.hexlify(addr_payload).decode()
        },
        "path": [{"pos": posn, "hash": binascii.hexlify(h).decode()} for (h, posn) in path]
    }
    return proof

def verify_leaf_proof(proof: Dict) -> bool:
    """
    Verify a single-leaf proof built by prove_leaf().
    Steps:
     - recompute preimage
     - compute L = SHA256(preimage)
     - iterate path updating running hash according to pos
     - compare to merkle_root
     - also check invoice_hash if present (caller ensures)
    Returns True iff valid.
    """
    leaf = proof.get("leaf")
    if not leaf:
        return False
    i = int(leaf["i"])
    txid_hex = leaf["txid"]
    amount = int(leaf["amount"])
    addr_payload_hex = leaf["addr_payload"]
    try:
        addr_payload = binascii.unhexlify(addr_payload_hex)
    except Exception:
        return False
    if len(addr_payload) != 21:
        return False
    # reconstruct recv_pub_compressed? Not needed: we can verify using addr_payload directly
    # Construct preimage: label || LE32(i) || txid || amount (8 le) || addr_payload
    try:
        preimage = b"leaf" + le32(i) + bytes.fromhex(txid_hex) + encode_le64(amount) + addr_payload
    except Exception:
        return False
    running = sha256(preimage)
    # apply path
    for step in proof.get("path", []):
        pos = step.get("pos")
        h_hex = step.get("hash")
        if pos not in ("L", "R"):
            return False
        try:
            sib = binascii.unhexlify(h_hex)
        except Exception:
            return False
        if len(sib) != 32:
            return False
        if pos == "L":
            running = sha256(running + sib)
        else:
            running = sha256(sib + running)
    root_claimed = binascii.unhexlify(proof.get("merkle_root"))
    return running == root_claimed

# Optional convenience: build manifest file and sign it
def persist_manifest(store: SimpleStore, manifest: Dict, signer_priv_int: Optional[int] = None):
    """
    Persist manifest canonically in store directory as manifest.json and append signed event.
    """
    manifest_path = store.dir / "manifest.json"
    # canonical JSON
    manifest_json = json.dumps(manifest, ensure_ascii=False, separators=(",", ":"), sort_keys=True)
    manifest_path.write_text(manifest_json, encoding="utf-8")
    evt = {"event": "manifest_saved", "invoice_hash": manifest["invoice_hash"], "merkle_root": manifest["merkle_root"], "count": manifest["count"]}
    append_log_event(store, evt, signer_priv_int=signer_priv_int)


import time
import json
from enum import Enum, auto
from typing import Dict, Any


# -------------------------
# Enums pour les états
# -------------------------

class NoteState(Enum):
    S0_CONSTRUCTED = auto()
    S1_SIGNED = auto()
    S2_QUEUED = auto()
    S3_BROADCAST = auto()
    S4_SEEN = auto()
    S5_CONFIRMED = auto()
    R_REISSUED = auto()
    C_CANCELLED = auto()
    O_ORPHANED = auto()
    X_OBSOLETE = auto()
    F_CONFLICT = auto()


class InvoiceState(Enum):
    I0_OPEN = auto()
    I1_FANOUT_PENDING = auto()
    I2_BUILDING = auto()
    I3_READY = auto()
    I4_BROADCASTING = auto()
    I5_CLOSING = auto()
    IF_INSUFFICIENT = auto()
    IE_EXPIRED = auto()
    IS_STOPPED = auto()
    IC_COMPLETED = auto()


# -------------------------
# Helper: timestamp
# -------------------------

def now_iso() -> str:
    return time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())


# -------------------------
# Audit log builder
# -------------------------

def log_reissue(invoice_hash: str, i: int, note_id: str, version: int,
                supersedes: str, txid_new: str,
                addr_recv: str, addr_change: str, fee: int, feerate: int,
                by: str, sig: str = "") -> Dict[str, Any]:
    return {
        "invoice_hash": invoice_hash,
        "i": i,
        "note_id": note_id,
        "event": "reissue",
        "version": version,
        "supersedes": supersedes,
        "txid_new": txid_new,
        "addr_recv": addr_recv,
        "addr_change": addr_change,
        "fee": fee,
        "feerate_used": feerate,
        "at": now_iso(),
        "by": by,
        "sig_alg": "secp256k1-sha256",
        "sig": sig
    }


def log_cancel(invoice_hash: str, i: int, note_id: str,
               reason: str, version: int, by: str, sig: str = "") -> Dict[str, Any]:
    return {
        "invoice_hash": invoice_hash,
        "i": i,
        "note_id": note_id,
        "event": "cancel",
        "reason": reason,  # hold_timeout|operator|expiry|insufficient_utxo
        "version": version,
        "at": now_iso(),
        "by": by,
        "sig_alg": "secp256k1-sha256",
        "sig": sig
    }


def log_conflict(invoice_hash: str, i: int, note_id: str,
                 txid: str, vout: int, by: str, sig: str = "") -> Dict[str, Any]:
    return {
        "invoice_hash": invoice_hash,
        "i": i,
        "note_id": note_id,
        "event": "conflict_external",
        "outpoint": {"txid": txid, "vout": vout},
        "at": now_iso(),
        "by": by,
        "sig_alg": "secp256k1-sha256",
        "sig": sig
    }


def log_orphaned(invoice_hash: str, i: int, note_id: str,
                 txid: str, by: str, sig: str = "") -> Dict[str, Any]:
    return {
        "invoice_hash": invoice_hash,
        "i": i,
        "note_id": note_id,
        "event": "orphaned",
        "txid": txid,
        "rebroadcast": True,
        "at": now_iso(),
        "by": by,
        "sig_alg": "secp256k1-sha256",
        "sig": sig
    }


# -------------------------
# Core Failure Handlers
# -------------------------

def handle_insufficient_utxo(invoice_state: InvoiceState, fanout_allowed: bool,
                             fanout_attempted: bool) -> Dict[str, Any]:
    """11.4 A - insufficient UTXOs"""
    if fanout_allowed and not fanout_attempted:
        # TODO: implement fan-out logic per §6.8
        fanout_attempted = True
        # retry build...
    else:
        invoice_state = InvoiceState.IF_INSUFFICIENT
        return {
            "event": "insufficient_utxo",
            "at": now_iso(),
            "fanout_attempted": fanout_attempted
        }


def handle_fee_change(note_state: NoteState, txid_old: str, version: int) -> Dict[str, Any]:
    """11.4 B - fee change before broadcast"""
    if note_state in [NoteState.S0_CONSTRUCTED, NoteState.S1_SIGNED, NoteState.S2_QUEUED]:
        note_state = NoteState.R_REISSUED
        # recompute fee, rebuild new tx, bump version...
        return {"event": "reissue", "supersedes": txid_old, "version": version + 1, "at": now_iso()}


def handle_conflict(note_state: NoteState, invoice_state: InvoiceState,
                    txid: str, vout: int) -> Dict[str, Any]:
    """11.4 C - conflict detected"""
    if note_state in [NoteState.S0_CONSTRUCTED, NoteState.S1_SIGNED, NoteState.S2_QUEUED]:
        note_state = NoteState.F_CONFLICT
        invoice_state = InvoiceState.I2_BUILDING  # or I5_CLOSING
        return {"event": "conflict_external", "outpoint": {"txid": txid, "vout": vout}, "at": now_iso()}


def handle_reorg(note_state: NoteState, txid: str) -> Dict[str, Any]:
    """11.4 D - reorg"""
    if note_state == NoteState.S5_CONFIRMED:
        note_state = NoteState.O_ORPHANED
        return {"event": "orphaned", "rebroadcast": True, "txid": txid, "at": now_iso()}


def handle_expiry(invoice_state: InvoiceState, notes: Dict[int, NoteState]) -> Dict[str, Any]:
    """11.4 E - expiry"""
    cancelled, broadcast, confirmed = 0, 0, 0
    for i, state in notes.items():
        if state in [NoteState.S0_CONSTRUCTED, NoteState.S1_SIGNED, NoteState.S2_QUEUED]:
            notes[i] = NoteState.C_CANCELLED
            cancelled += 1
        elif state in [NoteState.S3_BROADCAST, NoteState.S4_SEEN]:
            broadcast += 1
        elif state == NoteState.S5_CONFIRMED:
            confirmed += 1
    invoice_state = InvoiceState.IE_EXPIRED
    return {
        "event": "invoice_expired",
        "at": now_iso(),
        "counts": {"cancelled": cancelled, "broadcast": broadcast, "confirmed": confirmed}
    }



# ------------------------------
# Sections 9-13: Scheduling, receipts, failure handling, logging, security helpers
# ------------------------------
import time
from enum import Enum, auto
from copy import deepcopy

# ---------- small enums / types ----------
class NoteStatus(str, Enum):
    unsigned = "unsigned"
    signed = "signed"
    queued = "queued"
    broadcast = "broadcast"
    seen = "seen"
    confirmed = "confirmed"
    reissued = "reissued"
    cancelled = "cancelled"
    obsolete = "obsolete"
    orphaned = "orphaned"
    conflict = "conflict"

class InvoiceState(str, Enum):
    open = "open"
    fanout_pending = "fanout_pending"
    building = "building"
    ready = "ready"
    broadcasting = "broadcasting"
    closing = "closing"
    insufficient_utxo = "insufficient_utxo"
    expired = "expired"
    stopped = "stopped"
    completed = "completed"

# ---------- canonical/log helpers ----------
def sign_record_dict(record: Dict, signing_priv_int: int) -> Dict:
    """
    Attach signature triplet (sig_key, sig_alg, sig) to `record`.
    - record: dict (will not be mutated)
    - signing_priv_int: integer private scalar for identity key
    Returns a new dict with signature fields added and canonical bytes unchanged by caller.
    """
    rec = deepcopy(record)
    # compute canonical preimage without signature fields
    # our sign_canonical expects dict and a priv int; it returns hex DER signature
    sig_hex = sign_canonical(rec, signing_priv_int)
    # attach signer pubkey (compressed hex)
    pub_hex = binascii.hexlify(priv_to_pub_compressed(signing_priv_int)).decode()
    rec["sig_key"] = pub_hex
    rec["sig_alg"] = "secp256k1-sha256"
    rec["sig"] = sig_hex
    return rec


from dataclasses import dataclass
from typing import List, Optional

@dataclass
class NotePlan:
    index: int                 # note index i
    amount: int                # amount in sats
    recv_address: str          # Addrᴮ,ᵢ (recipient address)
    sender_change_address: str # Addrᴬ,ᵢ (payer change address)

@dataclass
class NoteResult:
    index: int                 # note index i
    tx_hex: str                # raw signed transaction (hex)
    txid: str                  # transaction id
    fee: int                   # fee paid (sats)
    size_bytes: int            # tx size in bytes
    change_amount: Optional[int] = None  # change amount, if any
    status: str = "unsigned"   # lifecycle status (matches §13.6 NoteMeta)

class LogStore:
    """
    Simple append-only log store that maintains prev_hash and seq.
    Each appended record is canonical JSON with signature fields added by the actor.
    Usage:
      logs = LogStore()
      logs.append(record_dict, signer_priv) -> returns appended_record (with prev_hash, seq, created_at, sig)
    """
    def __init__(self):
        self._records: List[Dict] = []

    def last_hash(self) -> Optional[bytes]:
        if not self._records:
            return None
        last = self._records[-1]
        # prev_hash stored as hex of prior record; compute hash of canonical bytes (without signature triplet) to compare
        return binascii.unhexlify(last.get("prev_hash", "00"*32)) if last.get("prev_hash") else None

    def append(self, record: Dict, signer_priv_int: int) -> Dict:
        rec = deepcopy(record)
        now = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
        rec["created_at"] = rec.get("created_at", now)
        rec["seq"] = (self._records[-1]["seq"] + 1) if self._records else 1

        # prev_hash is hash of canonical bytes of previous record (without its signature triplet).
        if self._records:
            prev = deepcopy(self._records[-1])
            # remove signature triplet from prev to compute prev_hash
            for f in ("sig_key", "sig_alg", "sig"):
                prev.pop(f, None)
            prev_bytes = canonical_json(prev)
            rec["prev_hash"] = binascii.hexlify(sha256(prev_bytes)).decode()
        else:
            rec["prev_hash"] = ""

        # Sign this record (signature added will be part of persist)
        signed = sign_record_dict(rec, signer_priv_int)
        self._records.append(signed)
        return signed

    def all(self) -> List[Dict]:
        return deepcopy(self._records)

# ---------- scheduling (9.5) ----------
def derive_pace_seed(Z: bytes, H_I: bytes) -> bytes:
    return sha256(Z + H_I + b"pace")

def schedule_from_policy(n_notes: int, now_ts: int, policy_broadcast: Dict, overrides: Optional[Dict],
                         Z: bytes, H_I: bytes) -> List[int]:
    """
    Deterministic schedule per §9.5. Returns list of timestamps (unix seconds) length n_notes for indices 0..N-1.
    policy_broadcast: dict from policy["broadcast"]
    overrides: optional invoice overrides (already validated)
    """
    # apply overrides (invoice cannot violate policy)
    b = policy_broadcast.copy()
    if overrides:
        b.update(overrides)

    authority = b.get("authority", "either")
    strategy = b.get("strategy_default", "paced")
    min_spacing_ms = int(b.get("min_spacing_ms", 0))
    max_spacing_ms = int(b.get("max_spacing_ms", min_spacing_ms))
    burst_size = int(b.get("burst_size", 1))
    burst_gap_ms = int(b.get("burst_gap_ms", 0))
    window_start = b.get("window_start", "")  # ISO-8601 or empty
    window_end = b.get("window_end", "")
    # convert window_start to ts if provided else now
    def parse_window(s):
        if not s:
            return now_ts
        try:
            # try parsing a simple Z timestamp
            t = int(time.mktime(time.strptime(s, "%Y-%m-%dT%H:%M:%SZ")))
            return t
        except Exception:
            return now_ts

    start_ts = parse_window(window_start)
    end_ts = parse_window(window_end) if window_end else None

    seed = derive_pace_seed(Z, H_I)

    def draw_ms(index: int, lo: int, hi: int) -> int:
        # deterministic unbiased draw in [lo, hi] using HKDF-like stream
        if lo == hi:
            return lo
        info = seed + b"pace_draw" + index.to_bytes(4, "little")
        u64 = int_from_bytes(sha256(info)[:8])
        rng = hi - lo + 1
        return lo + (u64 % rng)

    schedule = []
    if strategy == "all_at_once":
        t = max(now_ts, start_ts)
        schedule = [t for _ in range(n_notes)]
    elif strategy == "bursts":
        # partition indices into batches of size burst_size
        batch_times = []
        for k in range((n_notes + burst_size - 1) // burst_size):
            if k == 0:
                batch_time = max(now_ts, start_ts)
            else:
                batch_time = batch_times[-1] + (burst_gap_ms // 1000)
            batch_times.append(batch_time)
        for i in range(n_notes):
            batch_idx = i // burst_size
            base = batch_times[batch_idx]
            # tiny deterministic intra-batch offset in [0, min_spacing_ms]
            eps_ms = draw_ms(i, 0, min_spacing_ms)
            schedule.append(base + (eps_ms // 1000))
    else:  # paced
        t_prev = max(now_ts, start_ts)
        schedule.append(t_prev)
        for i in range(1, n_notes):
            d_ms = draw_ms(i, min_spacing_ms, max_spacing_ms)
            t_prev = t_prev + (d_ms // 1000)
            if end_ts and t_prev > end_ts:
                t_prev = end_ts
            schedule.append(t_prev)
    return schedule

# ---------- receipts / merkle proofs (10) ----------
def make_leaf_bytes(i: int, txid_hex: str, amount: int, recv_pub_serP: bytes) -> bytes:
    """
    Build the preimage for leaf i as specified:
    preimage := "leaf" ∥ LE32(i) ∥ txidᵢ ∥ amountᵢ (8-byte LE) ∥ addr_payload (version||h160)
    txid_hex expected as 64 hex characters (big-endian display). We convert to raw bytes.
    recv_pub_serP: compressed serP(Pᴮ,ᵢ) (33 bytes) so we can compute H160
    """
    if len(txid_hex) != 64:
        raise ValueError("txid must be 32-byte hex (64 chars)")
    label = b"leaf"
    le_i = le32(i)
    txid_bytes = binascii.unhexlify(txid_hex)  # big-endian bytes
    amt_le8 = (amount & ((1 << 64) - 1)).to_bytes(8, "little")
    h160_bytes = h160(recv_pub_serP)  # 20 bytes
    addr_payload = b"\x00" + h160_bytes  # ver||h160
    preimage = label + le_i + txid_bytes + amt_le8 + addr_payload
    return preimage

def make_leaf_hash(i: int, txid_hex: str, amount: int, recv_pub_serP: bytes) -> bytes:
    return sha256(make_leaf_bytes(i, txid_hex, amount, recv_pub_serP))

def receipts_manifest_from_results(results: List[NoteResult], recv_pub_serPs: Dict[int, bytes]) -> Dict:
    """
    Build manifest and merkle_root from list of NoteResult.
    recv_pub_serPs: mapping index->compressed pubkey bytes used to compute addr_payload (needed for leaf)
    Returns manifest dict per §10.4 with merkle_root hex, count, and entries (i, txid).
    """
    leaves = []
    index_map = {}
    for r in results:
        idx = r.index
        pub = recv_pub_serPs.get(idx)
        if pub is None:
            raise ValueError("missing recv pubkey for index %d" % idx)
        leaf = make_leaf_hash(idx, r.txid, r.amount, pub)
        leaves.append(leaf)
        index_map[idx] = leaf

    root = merkle_root(leaves)
    manifest = {
        "invoice_hash": binascii.hexlify(b"\x00"*32).decode(),  # placeholder: caller should set H_I
        "merkle_root": binascii.hexlify(root).decode(),
        "count": len(results),
        "entries": [{"i": r.index, "txid": r.txid} for r in results]
    }
    return manifest

def proof_for_index(leaves: List[bytes], index: int) -> List[Tuple[str, str]]:
    """
    Wrapper that returns proof as list of (hex sibling, 'L'|'R') as your merkle_proof() returns.
    """
    proof = merkle_proof(leaves, index)
    return [(binascii.hexlify(h).decode(), side) for h, side in proof]

# ---------- state transition helpers (11) ----------
def mark_note_seen(note_meta: Dict, txid_hex: str, ln_log: LogStore=None, signer_priv: Optional[int]=None):
    note_meta["txid"] = txid_hex
    note_meta["status"] = NoteStatus.seen.value
    note_meta["updated_at"] = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
    if ln_log and signer_priv:
        ev = {
            "invoice_hash": note_meta.get("invoice_hash", ""),
            "i": note_meta["i"],
            "note_id": note_meta.get("note_id", ""),
            "event": "seen",
            "txid": txid_hex
        }
        ln_log.append(ev, signer_priv)

def mark_note_confirmed(note_meta: Dict, depth: int, ln_log: LogStore=None, signer_priv: Optional[int]=None):
    note_meta["status"] = NoteStatus.confirmed.value
    note_meta["confirm_depth"] = depth
    note_meta["updated_at"] = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
    if ln_log and signer_priv:
        ev = {
            "invoice_hash": note_meta.get("invoice_hash", ""),
            "i": note_meta["i"],
            "note_id": note_meta.get("note_id", ""),
            "event": "confirmed",
            "confirm_depth": depth
        }
        ln_log.append(ev, signer_priv)

def reissue_note(note_meta: Dict, new_inputs: List[Dict], new_tx_hex: str, signer_priv: int, ln_log: LogStore):
    """
    Pre-broadcast reissue: preserve i, note_id, recv/change addrs; mark prior bytes obsolete; update version, status.
    new_inputs: list of inputs used in new candidate
    """
    old_tx = note_meta.get("txid", "")
    note_meta["supersedes"] = old_tx
    note_meta["version"] = note_meta.get("version", 1) + 1
    note_meta["txid"] = ""  # will be populated after broadcast/seen
    note_meta["status"] = NoteStatus.reissued.value
    note_meta["updated_at"] = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())

    rec = {
        "invoice_hash": note_meta.get("invoice_hash", ""),
        "i": note_meta["i"],
        "note_id": note_meta.get("note_id", ""),
        "event": "reissue",
        "version": note_meta["version"],
        "supersedes": note_meta.get("supersedes", ""),
        "txid_new": "",  # can be filled once available
        "addr_recv": note_meta.get("addr", ""),
        "addr_change": note_meta.get("change_addr", ""),
        "fee": note_meta.get("fee", 0),
        "feerate_used": note_meta.get("feerate_used", 0),
        "by": binascii.hexlify(priv_to_pub_compressed(signer_priv)).decode()
    }
    ln_log.append(rec, signer_priv)
    # caller should persist or broadcast new_tx_hex as needed
    return note_meta

def cancel_note(note_meta: Dict, reason: str, signer_priv: int, ln_log: LogStore):
    note_meta["status"] = NoteStatus.cancelled.value
    note_meta["updated_at"] = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
    rec = {
        "invoice_hash": note_meta.get("invoice_hash", ""),
        "i": note_meta["i"],
        "note_id": note_meta.get("note_id", ""),
        "event": "cancel",
        "reason": reason,
        "version": note_meta.get("version", 1),
        "by": binascii.hexlify(priv_to_pub_compressed(signer_priv)).decode()
    }
    ln_log.append(rec, signer_priv)
    return note_meta

def record_conflict(note_meta: Dict, outpoint: Dict, signer_priv: int, ln_log: LogStore):
    note_meta["status"] = NoteStatus.conflict.value
    note_meta["updated_at"] = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
    rec = {
        "invoice_hash": note_meta.get("invoice_hash", ""),
        "i": note_meta["i"],
        "note_id": note_meta.get("note_id", ""),
        "event": "conflict_external",
        "outpoint": outpoint,
        "by": binascii.hexlify(priv_to_pub_compressed(signer_priv)).decode()
    }
    ln_log.append(rec, signer_priv)
    return note_meta

def record_orphan(note_meta: Dict, txid: str, signer_priv: int, ln_log: LogStore):
    note_meta["status"] = NoteStatus.orphaned.value
    note_meta["updated_at"] = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
    rec = {
        "invoice_hash": note_meta.get("invoice_hash", ""),
        "i": note_meta["i"],
        "note_id": note_meta.get("note_id", ""),
        "event": "orphaned",
        "txid": txid,
        "rebroadcast": True,
        "by": binascii.hexlify(priv_to_pub_compressed(signer_priv)).decode()
    }
    ln_log.append(rec, signer_priv)
    return note_meta

# ---------- enforcement checks (13.2 / 13.9) ----------
def check_identity_anchor_separation(identity_pub_serP_hex: str, anchor_pub_serP_hex: str) -> bool:
    """
    Ensure identity pubkey != anchor pubkey (simple check).
    """
    return identity_pub_serP_hex.lower() != anchor_pub_serP_hex.lower()

def require_HI_unique(existing_HIs: set, H_I_hex: str):
    if H_I_hex in existing_HIs:
        raise ValueError("H_I reuse/collision detected")
    existing_HIs.add(H_I_hex)
    return True

# ---------- utilities for tests / integration ----------
def build_note_meta_from_plan(plan: NotePlan, H_I_hex: str) -> Dict:
    """
    Create initial NoteMeta dict for a plan (unsigned).
    """
    nid = binascii.hexlify(note_id(binascii.unhexlify(H_I_hex), plan.index)).decode() if H_I_hex else ""
    return {
        "i": plan.index,
        "note_id": nid,
        "invoice_hash": H_I_hex,
        "addr": plan.recv_address,
        "amount": plan.amount,
        "txid": "",
        "change_addr": plan.sender_change_address,
        "change_amount": 0,
        "size_bytes": None,
        "fee": None,
        "feerate_used": None,
        "status": NoteStatus.unsigned.value,
        "version": 1,
        "scheduled_at": "",
        "broadcast_at": "",
        "created_at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "updated_at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "prev_hash": "",
        "seq": 0
    }


import hashlib, hmac, time, random
from ecdsa import SECP256k1, ellipticcurve


# -------------------------------
# Helpers
# -------------------------------
def sha256(b: bytes) -> bytes:
    return hashlib.sha256(b).digest()

def int_from_sha256(data: bytes, n: int) -> int:
    """Return scalar in [1,n-1]"""
    i = int.from_bytes(sha256(data), "big") % n
    if i == 0:
        raise ValueError("Reject-zero derivation")
    return i


# -------------------------------
# Domain-separated key derivations
# -------------------------------
curve = SECP256k1
G = curve.generator
n = curve.order


def derive_recv_key(B: ellipticcurve.Point, Z: bytes, H_I: bytes, i: int) -> ellipticcurve.Point:
    """
    Recipient key derivation (domain = "recv")
    Pᴮ,ᵢ = B + tᵢ·G
    """
    t_i = int_from_sha256(Z + H_I + b"recv" + i.to_bytes(4, "little"), n)
    return B + t_i * G


def derive_snd_key(A: ellipticcurve.Point, Z: bytes, H_I: bytes, i: int) -> ellipticcurve.Point:
    """
    Sender-change key derivation (domain = "snd")
    Pᴬ,ᵢ = A + sᵢ·G
    """
    s_i = int_from_sha256(Z + H_I + b"snd" + i.to_bytes(4, "little"), n)
    return A + s_i * G


# -------------------------------
# Broadcast scheduling (M₂, M₆)
# -------------------------------
def deterministic_jitter(seed: bytes, i: int, window_s: int) -> int:
    """
    Derive deterministic jitter per note index.
    Uses H(Z || Hᴵ || "pace" || i).
    """
    h = sha256(seed + b"pace" + i.to_bytes(4, "little"))
    return int.from_bytes(h, "big") % window_s


def schedule_broadcasts(N: int, start_time: int, seed: bytes,
                        window_s: int = 300, burst_size: int = 3) -> list[int]:
    """
    Build paced/bursty broadcast schedule with jitter.
    Returns list of UNIX timestamps per note index.
    """
    schedule = []
    for i in range(N):
        jitter = deterministic_jitter(seed, i, window_s)
        # Assign bursts
        burst_offset = (i // burst_size) * window_s
        t_i = start_time + burst_offset + jitter
        schedule.append(t_i)
    return schedule


# -------------------------------
# Privacy Mitigations
# -------------------------------
def enforce_no_reuse_within_invoice(inputs_per_note: list[list[str]]):
    """
    Ensure no UTXO is reused across notes of the same invoice.
    """
    seen = set()
    for idx, note_inputs in enumerate(inputs_per_note):
        for utxo in note_inputs:
            if utxo in seen:
                raise ValueError(f"UTXO reuse detected at note {idx}")
            seen.add(utxo)
    return True


def publish_bounds(v_min: int, v_max: int, loosen: int = 0):
    """
    Publish wider interval than actual amounts.
    """
    return (v_min - loosen, v_max + loosen)

# ------------------------------
# Helpers: hashing / misc
# ------------------------------
def sha256(b: bytes) -> bytes:
    return hashlib.sha256(b).digest()

def dbl_sha256(b: bytes) -> bytes:
    return hashlib.sha256(hashlib.sha256(b).digest()).digest()

def ripemd160(b: bytes) -> bytes:
    h = hashlib.new("ripemd160")
    h.update(b)
    return h.digest()

def h160(b: bytes) -> bytes:
    return ripemd160(sha256(b))

def int_from_bytes(b: bytes) -> int:
    return int.from_bytes(b, "big")

def i2b32(i: int) -> bytes:
    return i.to_bytes(32, "big")

# Simple HKDF (extract+expand) for deterministic derivations
def hkdf_extract(salt: bytes, ikm: bytes) -> bytes:
    return hmac.new(salt, ikm, hashlib.sha256).digest()

def hkdf_expand(prk: bytes, info: bytes, l: int) -> bytes:
    t = b""
    okm = b""
    block = 1
    while len(okm) < l:
        t = hmac.new(prk, t + info + bytes([block]), hashlib.sha256).digest()
        okm += t
        block += 1
    return okm[:l]

def hkdf(ikm: bytes, salt: bytes, info: bytes, l: int) -> bytes:
    prk = hkdf_extract(salt, ikm)
    return hkdf_expand(prk, info, l)

# ------------------------------
# EC helpers (compressed pubkeys)
# ------------------------------
def point_to_bytes_compressed(P: ellipticcurve.Point) -> bytes:
    x = P.x()
    y = P.y()
    return (b"\x02" if y % 2 == 0 else b"\x03") + x.to_bytes(32, "big")

def priv_to_pub_compressed(priv: int) -> bytes:
    P = priv * G
    return point_to_bytes_compressed(P)

def bytes_to_point(b: bytes) -> ellipticcurve.Point:
    if len(b) != 33 or b[0] not in (2, 3):
        raise ValueError("invalid compressed pub")
    x = int.from_bytes(b[1:], "big")
    curve = SECP.curve
    alpha = (x * x * x + 7) % curve.p()
    beta = pow(alpha, (curve.p() + 1) // 4, curve.p())
    y = beta
    if (y % 2) != (b[0] % 2):
        y = (-y) % curve.p()
    return ellipticcurve.Point(curve, x, y)

def pubkey_add_tweak(pubkey_compressed: bytes, tweak: int) -> bytes:
    P = bytes_to_point(pubkey_compressed)
    Q = P + tweak * G
    return point_to_bytes_compressed(Q)

def priv_add_tweak(priv: int, tweak: int) -> int:
    return (priv + tweak) % N

def ecdh_shared(priv_a: int, pub_b_compressed: bytes) -> bytes:
    P = bytes_to_point(pub_b_compressed)
    S = priv_a * P
    return i2b32(S.x())

def p2pkh_address_from_pubkey_compressed(pub_compressed: bytes) -> str:
    payload = b"\x00" + h160(pub_compressed)
    checksum = dbl_sha256(payload)[:4]
    return base58.b58encode(payload + checksum)

# ------------------------------
# Deterministic derivation utilities
# ------------------------------
def canonical_invoice_hash(invoice: Dict) -> bytes:
    # Use the canonical_json function (same bytes used for signing/verifying)
    return sha256(canonical_json(invoice))


def derive_scalar(Z: bytes, H_I: bytes, tag: str, i: int) -> int:
    info = b"NNP/scalar/" + tag.encode() + b"/" + i.to_bytes(8, "big")
    t = hkdf(ikm=Z, salt=H_I, info=info, l=32)
    k = int_from_bytes(t) % N
    if k == 0:
        k = 1
    return k

def prng_bytes(Z: bytes, H_I: bytes, tag: str, l: int) -> bytes:
    info = b"NNP/prng/" + tag.encode()
    return hkdf(ikm=Z, salt=H_I, info=info, l=l)

def derive_permutation(Z: bytes, H_I: bytes, n: int) -> List[int]:
    seed = prng_bytes(Z, H_I, "perm", 32)
    rnd = random.Random(int_from_bytes(seed))
    idxs = list(range(n))
    rnd.shuffle(idxs)
    return idxs

# ------------------------------
# Bounded splitting
# ------------------------------
def split_total_into_bounded_notes(total: int, vmin: int, vmax: int, Z: bytes, H_I: bytes) -> List[int]:
    assert vmin > 0 and vmax >= vmin
    rnd = random.Random(int_from_bytes(prng_bytes(Z, H_I, "split", 32)))
    remaining = total
    parts: List[int] = []
    while remaining > 0:
        hi = min(vmax, remaining)
        lo = min(vmin, hi)
        if remaining <= vmax:
            take = remaining
        else:
            take = rnd.randint(lo, hi)
        if remaining - take != 0 and (remaining - take) < vmin:
            take = max(lo, remaining - vmin)
        parts.append(take)
        remaining -= take
    perm = derive_permutation(Z, H_I, len(parts))
    permuted = [0] * len(parts)
    for i, p in enumerate(perm):
        permuted[p] = parts[i]
    return permuted

# ------------------------------
# Merkle receipts
# ------------------------------
def merkle_parent(a: bytes, b: bytes) -> bytes:
    return dbl_sha256(a + b)

def merkle_root(leaves: List[bytes]) -> bytes:
    if not leaves:
        return b"\x00" * 32
    level = leaves[:]
    while len(level) > 1:
        if len(level) % 2 == 1:
            level.append(level[-1])
        level = [merkle_parent(level[i], level[i+1]) for i in range(0, len(level), 2)]
    return level[0]

def merkle_proof(leaves: List[bytes], index: int) -> List[Tuple[bytes, str]]:
    path = []
    idx = index
    level = leaves[:]
    while len(level) > 1:
        if len(level) % 2 == 1:
            level.append(level[-1])
        pair_index = idx ^ 1
        side = 'R' if (idx % 2 == 0) else 'L'
        path.append((level[pair_index], side))
        next_level = []
        for i in range(0, len(level), 2):
            next_level.append(merkle_parent(level[i], level[i+1]))
        level = next_level
        idx //= 2
    return path



# ------------------------------
# UTXO helpers and selection
# ------------------------------
@dataclass
class SimpleUTXO:
    txid: str
    vout: int
    amount: int
    script: Optional[str]

class MyUnspent:
    def __init__(self, txid: str, txindex: int, amount: int, confirmations: int = 0, script: Optional[str] = None):
        self.txid = txid
        self.txindex = txindex
        self.amount = amount
        self.confirmations = confirmations
        self.script = script
        self.scriptcode = script

def fetch_utxos_for_key(k: Key) -> List[SimpleUTXO]:
    unspents = k.get_unspents()
    utxos: List[SimpleUTXO] = []
    for u in unspents:
        script_hex = getattr(u, "script", None) or getattr(u, "scriptcode", None) or None
        utxos.append(SimpleUTXO(txid=u.txid, vout=u.txindex, amount=u.amount, script=script_hex))
    utxos.sort(key=lambda x: (x.amount, x.txid, x.vout))
    return utxos

def make_unspent_objects(selected: List[SimpleUTXO]) -> List[MyUnspent]:
    out: List[MyUnspent] = []
    for u in selected:
        out.append(MyUnspent(txid=u.txid, txindex=u.vout, amount=u.amount, confirmations=0, script=u.script))
    return out

# ------------------------------
# Coin selection (deterministic, disjoint) -- replace the buggy single-selection code
# ------------------------------
def select_inputs_for_amount(utxos: List[SimpleUTXO], target: int, fee_floor: int, dust_limit: int) -> Tuple[List[SimpleUTXO], int, int]:
    need = target + fee_floor

    # 1) Single UTXO >= need, choisir le plus gros pour éviter multiples inputs
    singles = [u for u in utxos if u.amount >= need]
    if singles:
        singles.sort(key=lambda x: -x.amount)  # plus gros en premier
        chosen = singles[0]
        change = chosen.amount - need
        if change == 0 or change >= dust_limit:
            return [chosen], change, fee_floor
        else:
            fee_used = fee_floor + change
            return [chosen], 0, fee_used

    # 2) Sinon, accumuler pour atteindre need
    pool = sorted(utxos, key=lambda x: -x.amount)  # gros en premier pour moins d'inputs
    acc = 0
    chosen = []
    for u in pool:
        chosen.append(u)
        acc += u.amount
        if acc >= need:
            change = acc - need
            if change == 0 or change >= dust_limit:
                return chosen[:], change, fee_floor
            else:
                fee_used = fee_floor + change
                return chosen[:], 0, fee_used

    # Rien ne suffit
    raise ValueError(f"Insufficient funds: need {need}, have {sum(u.amount for u in utxos)}")

@dataclass
class NotePlan:
    index: int
    amount: int
    recv_address: str
    sender_change_address: Optional[str]


def reserve_disjoint_inputs(all_utxos: List[SimpleUTXO], plans: List[NotePlan],
                            fee_floor: int, dust_limit: int, Z: bytes, H_I: bytes):
    """
    Select UTXOs per plan, avoiding double use.
    Returns a list of (selected_utxos, change, fee_used) for each plan.
    """
    remaining_utxos = all_utxos[:]  # copy list to avoid modifying original
    results = []

    for plan in plans:
        try:
            selected_utxos, change, fee_used = select_inputs_for_amount(
                remaining_utxos, target=plan.amount, fee_floor=fee_floor, dust_limit=dust_limit
            )
        except ValueError as e:
            raise RuntimeError(f"failed to select inputs for plan {plan.index}: {e}")

        # remove used UTXOs so they aren't reused
        for u in selected_utxos:
            remaining_utxos.remove(u)

        results.append((selected_utxos, change, fee_used))

    return results

# ------------------------------
# Data classes: keys / wallets / invoice
# ------------------------------
@dataclass
class Identity:
    priv: int
    def sk(self) -> SigningKey:
        return SigningKey.from_secret_exponent(self.priv, curve=SECP)
    def vk_compressed(self) -> bytes:
        return self.sk().get_verifying_key().to_string("compressed")

@dataclass
class Anchor:
    priv: int
    def pub_compressed(self) -> bytes:
        return priv_to_pub_compressed(self.priv)
    def addr(self) -> str:
        return p2pkh_address_from_pubkey_compressed(self.pub_compressed())

@dataclass
class Invoice:
    payer: str
    payee: str
    amount_sats: int
    currency: str
    memo: str
    terms: Dict
    def to_dict(self) -> Dict:
        return asdict(self)

@dataclass
class PayerWallet:
    identity: Identity
    anchor: Anchor
    key: Key
    @staticmethod
    def from_wif(identity_wif: str, anchor_wif: str, spend_wif: str):
        id_key = Key(identity_wif); anc_key = Key(anchor_wif); spend_key = Key(spend_wif)
        return PayerWallet(identity=Identity(id_key.to_int()), anchor=Anchor(anc_key.to_int()), key=spend_key)

@dataclass
class PayeeWallet:
    identity: Identity
    anchor: Anchor
    @staticmethod
    def from_wif(identity_wif: str, anchor_wif: str):
        id_key = Key(identity_wif); anc_key = Key(anchor_wif)
        return PayeeWallet(identity=Identity(id_key.to_int()), anchor=Anchor(anc_key.to_int()))

@dataclass
class NotePlan:
    index: int
    amount: int
    recv_address: str
    sender_change_address: Optional[str]

@dataclass
class NoteResult:
    index: int
    tx_hex: str
    txid: str
    amount: int
    recv_address: str
from bitsv.network.services import NetworkAPI
from bitsv import Key
from bitsv.network.meta import Unspent

def convert_utxos(raw_utxos: List[SimpleUTXO], key: Key):
    """
    Convert list of raw utxos (SimpleUTXO instances) to bitsv Unspent objects for BSV
    """
    unspents = []
    for u in raw_utxos:
        unspents.append(
            Unspent(
                amount=u.amount,         # in satoshis
                confirmations=1,         # or fetch actual confirmations
                txid=u.txid,
                txindex=u.vout
            )
        )
    return unspents

# ------------------------------
# Core Engine
# ------------------------------
class NegotiatedNotes:
    def __init__(self, payer: PayerWallet, payee: PayeeWallet, invoice: Invoice):
        self.payer = payer
        self.payee = payee
        self.invoice = invoice
        self.H_I = canonical_invoice_hash(invoice.to_dict())
        self.Z = ecdh_shared(self.payer.identity.priv, self.payee.identity.sk().get_verifying_key().to_string("compressed"))

    def derive_recv_address(self, i: int) -> Tuple[str, int]:
        t = derive_scalar(self.Z, self.H_I, "recv", i)
        recv_pub = pubkey_add_tweak(self.payee.anchor.pub_compressed(), t)
        return p2pkh_address_from_pubkey_compressed(recv_pub), t

    def derive_sender_change_address(self, i: int) -> Tuple[str, int]:
        t = derive_scalar(self.Z, self.H_I, "snd", i)
        priv_change = priv_add_tweak(self.payer.anchor.priv, t)
        print("Change private key (int):", priv_change)
        pub_change = priv_to_pub_compressed(priv_change)
        addr = p2pkh_address_from_pubkey_compressed(pub_change)
        print("Change address:", addr)
        return addr, priv_change

    def plan_notes(self, vmin: int, vmax: int, fee_floor: int, dust_limit: int) -> List[NotePlan]:
        amounts = split_total_into_bounded_notes(self.invoice.amount_sats, vmin, vmax, self.Z, self.H_I)
        plans: List[NotePlan] = []
        for i, a in enumerate(amounts):
            recv_addr, _ = self.derive_recv_address(i)
            chg_addr, _ = self.derive_sender_change_address(i)
            plans.append(NotePlan(index=i, amount=a, recv_address=recv_addr, sender_change_address=chg_addr))
        return plans

    def build_and_sign(self, plans: List[NotePlan], fee_floor: int, dust_limit: int) -> List[NoteResult]:
     """
    Build a single combined transaction to cover all plans using available UTXOs.
    """
     raw_utxos = fetch_utxos_for_key(self.payer.key)  # your SimpleUTXO list
     utxos = convert_utxos(raw_utxos, self.payer.key)  # convert to Unspent

# now use `utxos` in create_transaction

     total_amount = sum(p.amount for p in plans)

    # Sort UTXOs descending
     sorted_utxos = sorted(utxos, key=lambda x: -x.amount)

     selected_utxos = []
     accumulated = 0
     for u in sorted_utxos:
        selected_utxos.append(u)
        accumulated += u.amount
        # Note: here we use total_amount + FEE_FLOOR as a minimal starting point
        if accumulated >= total_amount + fee_floor:
            break

     if accumulated < total_amount + fee_floor:
        raise RuntimeError(f"Insufficient funds: need {total_amount + fee_floor}, available {accumulated}")

    # The dynamic fee will be recalculated by bitsv.create_transaction,
    # so let's check if selected_utxos sum is sufficient:
     try:
        outputs_list = [(plan.recv_address, plan.amount, 'satoshi') for plan in plans]
        change = accumulated - total_amount - fee_floor
        if change >= dust_limit:
            outputs_list.append((plans[0].sender_change_address, change, 'satoshi'))

        tx_hex = self.payer.key.create_transaction(
            outputs=outputs_list,
            unspents=selected_utxos,
            fee=fee_floor  # bitsv will adjust automatically
        )
     except Exception as e:
        # If fee recalculation fails, include all remaining UTXOs
        selected_utxos = sorted_utxos  # pick all available
        try:
            tx_hex = self.payer.key.create_transaction(
                outputs=outputs_list,
                unspents=selected_utxos,
                fee=fee_floor
            )
        except Exception as e2:
            raise RuntimeError(f"failed to build combined tx even with all UTXOs: {e2}")

     txid = bytes_to_hex(dbl_sha256(hex_to_bytes(tx_hex))[::-1])
     results = [
        NoteResult(index=plan.index, tx_hex=tx_hex, txid=txid, amount=plan.amount, recv_address=plan.recv_address)
        for plan in plans
    ]
     return results

    def create_signed_note_tx(self, payer_key: Key, inputs: List[SimpleUTXO], amount_sats: int, recv_address: str, change_address: Optional[str], fee: int) -> str:
        outputs = [(recv_address, amount_sats, "satoshi")]
        unspents = make_unspent_objects(inputs)
        # bitsv Key.create_transaction expects 'fee' and optional 'leftover'
        kwargs = {"outputs": outputs, "unspents": unspents, "fee": fee}
        if change_address:
            kwargs["leftover"] = change_address
        tx_hex = payer_key.create_transaction(**kwargs)
        return tx_hex

    
    def broadcast_all(self, txs: List[NoteResult]) -> Dict[int, str]:
        statuses = {}
        net = NetworkAPI("main")
        for n in txs:
            try:
                net.broadcast_tx(n.tx_hex)

                statuses[n.index] = f"success:{n.txid}"
            except Exception as e:
                statuses[n.index] = f"error:{e}"
        return statuses

    @staticmethod
    def receipts(results: List[NoteResult]) -> Dict:
        leaves = []
        for r in results:
            payload = json.dumps({"i": r.index, "txid": r.txid, "amt": r.amount, "addr": r.recv_address}, sort_keys=True, separators=(",", ":")).encode("utf-8")
            leaves.append(dbl_sha256(payload))
        root = merkle_root(leaves)
        manifest = [{"i": r.index, "txid": r.txid} for r in results]
        proofs = {}
        for i in range(len(leaves)):
            proofs[i] = [(binascii.hexlify(sib).decode(), side) for (sib, side) in merkle_proof(leaves, i)]
        return {"merkle_root": binascii.hexlify(root).decode(), "manifest": manifest, "proofs": proofs}

# ------------------------------
# CLI / Demo entrypoint
# ------------------------------
if __name__ == "__main__":
    # CONFIG - set real WIFs via env or edit here
    # Directly assign WIF keys instead of reading from environment
    PAYER_ID_WIF    = "L1aW4aubDFB7yfras2S1mMEF1S1q2..."   # replace with actual WIF
    PAYER_ANC_WIF   = "Kx1234abcd5678efgh9012ijkl..."       # replace with actual WIF
    PAYER_SPEND_WIF = "L5BmYH5gF...actual spend WIF..."      # replace with actual WIF
    PAYEE_ID_WIF    = "Ky9876mnop3456qrst7890uvwx..."       # replace with actual WIF
    PAYEE_ANC_WIF   = "L3zxy123abcd456efgh789ijkl..."       # replace with actual WIF


    if not (PAYER_ID_WIF and PAYER_ANC_WIF and PAYER_SPEND_WIF and PAYEE_ID_WIF and PAYEE_ANC_WIF):
        raise SystemExit("Set PAYER_ID_WIF, PAYER_ANC_WIF, PAYER_SPEND_WIF, PAYEE_ID_WIF, PAYEE_ANC_WIF in environment.")

    payer = PayerWallet.from_wif(PAYER_ID_WIF, PAYER_ANC_WIF, PAYER_SPEND_WIF)
    payee = PayeeWallet.from_wif(PAYEE_ID_WIF, PAYEE_ANC_WIF)

    invoice = Invoice(
        payer="AliceCo",
        payee="BobShop",
        amount_sats=int(os.environ.get("INVOICE_AMOUNT_SATS", "15000")),  # default 15k sats
        currency="BSV",
        memo="order-demo",
        terms={"expiry": "2025-12-31T23:59:59Z", "min_conf": 1}
    )

    # POLICY (tweak as needed)
    VMIN = int(os.environ.get("VMIN", "1000"))
    VMAX = int(os.environ.get("VMAX", "6000"))
    FEE_FLOOR = int(os.environ.get("FEE_FLOOR", "200"))
    DUST_LIMIT = int(os.environ.get("DUST_LIMIT", "546"))

    engine = NegotiatedNotes(payer, payee, invoice)
    plans = engine.plan_notes(VMIN, VMAX, FEE_FLOOR, DUST_LIMIT)

    # optional debug: print plan & UTXOs
    utxos = fetch_utxos_for_key(payer.key)
    print(json.dumps({
        "invoice": invoice.to_dict(),
        "plans": [asdict(p) for p in plans],
        "available_utxos": [{"txid": u.txid, "vout": u.vout, "amount": u.amount} for u in utxos]
    }, indent=2))

    # Build & sign
    try:
        results = engine.build_and_sign(plans, FEE_FLOOR, DUST_LIMIT)
    except Exception as e:
        print("build_and_sign error:", repr(e))
        raise

    receipts = engine.receipts(results)

    # print outputs
    print(json.dumps({
        "results": [asdict(r) for r in results],
        "receipts": receipts
    }, indent=2))

    # optionally broadcast (uncomment to broadcast)
    statuses = engine.broadcast_all(results)

    print("broadcast_statuses:", statuses)
    print("Donate to keep this project alive: 1ERc7xAG9oDZtw4a9x7oTGYxz6PLzqfM2Z")

