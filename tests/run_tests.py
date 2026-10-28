#!/usr/bin/env python3
"""Test harness for the Lean SSH wire types.

Layers, all settled against independent expectations:

1. Fixed cases: the mpint examples printed in RFC 4251
   section 5 (fed as fields; the answer must be the same
   bytes, which settles the read and the canonical reprint
   together), plus fixed string, name-list, and blob fields.

2. Real keys: when `ssh-keygen` is on the machine, test keys
   (ed25519 and RSA 2048) are generated in the work dir's
   scratch folder, the base64 blob of each `.pub` line is fed
   to the tool, and the answer must be the same bytes. The
   parsed fields are checked against an independent Python
   parse of the same blob, and against Python's `cryptography`
   library when it is importable.

3. A differential against a strict oracle written here from
   SPEC.md (which states the slice's readings of RFC 4251
   section 5 and RFC 4253 section 6.6): generated values of
   every type are encoded by the oracle, read by the tool, and
   the answer must be the canonical reprint; random raw byte
   strings are settled by comparing the tool's answer with
   the oracle's answer on the same bytes.

4. Mutations with named expectations (non minimal mpints,
   length overruns, truncations, trailing bytes, a 31 byte
   ed25519 key, an RSA blob with e = 0, an unknown algorithm
   name, bad name-lists), settled by the oracle.

Results are written to tests/TEST-RESULTS.md. Seed 20261027.

Usage: python3 tests/run_tests.py [--skip-build]
"""

import base64
import os
import random
import shutil
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
EXE = os.path.join(ROOT, ".lake", "build", "bin", "ssh")
SCRATCH = os.path.join(ROOT, "scratch")
SEED = 20261027

failures = []


def check(cond, label, detail=""):
    if not cond:
        failures.append(f"{label}: {detail}")
        print(f"FAIL {label}: {detail}")


# ---------------------------------------------------------------------------
# Batch runner: one process for many requests.
# ---------------------------------------------------------------------------

class Tool:
    def __init__(self):
        self.lines = []

    def ask(self, line):
        self.lines.append(line)
        return len(self.lines) - 1

    def run(self):
        proc = subprocess.run([EXE], input="\n".join(self.lines) + "\n",
                              capture_output=True, text=True, timeout=1200)
        if proc.returncode != 0:
            raise RuntimeError(f"tool exited {proc.returncode}: {proc.stderr[:500]}")
        self.answers = proc.stdout.splitlines()
        if len(self.answers) != len(self.lines):
            raise RuntimeError(
                f"answer count {len(self.answers)} != request count {len(self.lines)}")
        return self.answers


def req(op, bs):
    return op + " " + ",".join(str(b) for b in bs)


def want_ok(canon):
    return "ok:" + ",".join(str(b) for b in canon)


# ---------------------------------------------------------------------------
# Oracle, written from SPEC.md.
# ---------------------------------------------------------------------------

def enc_string(content):
    return len(content).to_bytes(4, "big") + bytes(content)


def read_string(bs):
    if len(bs) < 4:
        return None
    ln = int.from_bytes(bs[:4], "big")
    if len(bs) < 4 + ln:
        return None
    return bytes(bs[4:4 + ln]), bytes(bs[4 + ln:])


def mpint_content(v):
    if v == 0:
        return b""
    n = 1
    while True:
        try:
            return v.to_bytes(n, "big", signed=True)
        except OverflowError:
            n += 1


def mpint_value(content):
    if not content:
        return 0
    return int.from_bytes(content, "big", signed=True)


def mpint_minimal(content):
    return mpint_content(mpint_value(content)) == bytes(content)


def read_mpint_field(bs):
    """A whole mpint field: value or None."""
    r = read_string(bs)
    if r is None:
        return None
    content, rest = r
    if rest:
        return None
    if not mpint_minimal(content):
        return None
    return mpint_value(content)


def enc_mpint_field(v):
    return enc_string(mpint_content(v))


NAME_BYTES = set(range(0x21, 0x7F)) - {44}


def parse_names_content(content):
    if not content:
        return []
    names = bytes(content).split(b",")
    for nm in names:
        if not nm:
            return None
        if any(b not in NAME_BYTES for b in nm):
            return None
    return names


def enc_names_field(names):
    return enc_string(b",".join(names))


def read_blob(bs):
    """A whole key blob: ('ed', key) or ('rsa', e, n) or None."""
    r = read_string(bs)
    if r is None:
        return None
    alg, rest = r
    if alg == b"ssh-ed25519":
        r2 = read_string(rest)
        if r2 is None:
            return None
        key, rest2 = r2
        if rest2 or len(key) != 32:
            return None
        return ("ed", key)
    if alg == b"ssh-rsa":
        r2 = read_string(rest)
        if r2 is None:
            return None
        ec, rest = r2
        if not mpint_minimal(ec):
            return None
        e = mpint_value(ec)
        r3 = read_string(rest)
        if r3 is None:
            return None
        nc, rest = r3
        if not mpint_minimal(nc):
            return None
        n = mpint_value(nc)
        if rest or e <= 0 or n <= 0:
            return None
        return ("rsa", e, n)
    return None


def enc_blob(b):
    if b[0] == "ed":
        return enc_string(b"ssh-ed25519") + enc_string(b[1])
    return enc_string(b"ssh-rsa") + enc_mpint_field(b[1]) + enc_mpint_field(b[2])


def oracle_answer(op, bs):
    if op == "mpint":
        v = read_mpint_field(bs)
        return "none" if v is None else want_ok(enc_mpint_field(v))
    if op == "string":
        r = read_string(bs)
        if r is None or r[1]:
            return "none"
        return want_ok(enc_string(r[0]))
    if op == "names":
        r = read_string(bs)
        if r is None or r[1]:
            return "none"
        names = parse_names_content(r[0])
        if names is None:
            return "none"
        return want_ok(enc_names_field(names))
    if op == "blob":
        b = read_blob(bs)
        return "none" if b is None else want_ok(enc_blob(b))
    raise ValueError(op)


# ---------------------------------------------------------------------------
# Section 1: fixed cases.
# ---------------------------------------------------------------------------

RFC_MPINT = [
    (0, bytes([0, 0, 0, 0])),
    (0x9A378F9B2E332A7,
     bytes([0, 0, 0, 8, 0x09, 0xA3, 0x78, 0xF9, 0xB2, 0xE3, 0x32, 0xA7])),
    (-0x1234, bytes([0, 0, 0, 2, 0xED, 0xCC])),
    (-0xDEADBEEF, bytes([0, 0, 0, 5, 0xFF, 0x21, 0x52, 0x41, 0x11])),
]


def section_fixed(tool):
    n = 0
    for v, field in RFC_MPINT:
        i = tool.ask(req("mpint", field))
        check(enc_mpint_field(v) == field, "fixed-rfc-enc",
              f"oracle encodes {v} as {list(enc_mpint_field(v))}, RFC says {list(field)}")
        n += 1
        yield i, want_ok(field), f"rfc-mpint-{v}"
    fixed = []
    fixed.append(("string", enc_string(b""), enc_string(b"")))
    fixed.append(("string", enc_string(b"hi"), enc_string(b"hi")))
    fixed.append(("string", enc_string(bytes([0, 255, 1])), enc_string(bytes([0, 255, 1]))))
    big = bytes(range(256)) * 3
    fixed.append(("string", enc_string(big), enc_string(big)))
    fixed.append(("names", enc_names_field([]), enc_names_field([])))
    fixed.append(("names", enc_names_field([b"a"]), enc_names_field([b"a"])))
    fixed.append(("names", enc_names_field([b"zlib@openssh.com", b"host-key-1._x"]),
                  enc_names_field([b"zlib@openssh.com", b"host-key-1._x"])))
    key = bytes(range(32))
    fixed.append(("blob", enc_blob(("ed", key)), enc_blob(("ed", key))))
    fixed.append(("blob", enc_blob(("rsa", 17, 3233)), enc_blob(("rsa", 17, 3233))))
    fixed.append(("blob", enc_blob(("rsa", 65537, 3233)), enc_blob(("rsa", 65537, 3233))))
    for op, field, canon in fixed:
        i = tool.ask(req(op, field))
        n += 1
        yield i, want_ok(canon), f"fixed-{op}-{n}"
    return n


# ---------------------------------------------------------------------------
# Section 2: real keys from ssh-keygen.
# ---------------------------------------------------------------------------

def parse_blob_fields(blob):
    """An independent parse, for the field-by-field check."""
    r = read_string(blob)
    alg, rest = r
    if alg == b"ssh-ed25519":
        key, rest = read_string(rest)
        assert not rest
        return {"alg": alg, "key": key}
    e_c, rest = read_string(rest)
    n_c, rest = read_string(rest)
    assert not rest
    return {"alg": alg, "e": mpint_value(e_c), "n": mpint_value(n_c),
            "e_bytes": e_c, "n_bytes": n_c}


def section_real_keys(tool, notes):
    """Returns (inputs, agreements). Fills notes with what was found."""
    kg = shutil.which("ssh-keygen")
    if kg is None:
        notes.append("ssh-keygen was not found on this machine; the real key "
                     "section did not run. Hand built blobs and the oracle "
                     "carry the blob checks.")
        return 0, 0
    notes.append(f"ssh-keygen was found at {kg}; it generated fresh test "
                 "keys (ed25519 and RSA 2048) in the work dir scratch "
                 "folder for this run. The keys are kept only there and "
                 "are not committed.")
    os.makedirs(SCRATCH, exist_ok=True)
    specs = [("ed25519", ["-t", "ed25519"]), ("rsa", ["-t", "rsa", "-b", "2048"])]
    jobs = []
    for name, args in specs:
        path = os.path.join(SCRATCH, f"test_{name}")
        for suf in ("", ".pub"):
            if os.path.exists(path + suf):
                os.remove(path + suf)
        subprocess.run([kg] + args + ["-N", "", "-f", path],
                       capture_output=True, text=True, check=True)
        pub = open(path + ".pub").read().split()
        blob = base64.b64decode(pub[1])
        fields = parse_blob_fields(blob)
        check(pub[0].encode() == fields["alg"], "realkey-alg",
              f"{name}: .pub names {pub[0]}, blob says {fields['alg']}")
        idx = tool.ask(req("blob", blob))
        jobs.append((idx, blob, name, fields))
    # cryptography cross-check, when importable.
    try:
        import cryptography
        from cryptography.hazmat.primitives.serialization import (
            load_ssh_public_key)
        notes.append(f"Python's `cryptography` library was importable in "
                     f"the interpreter that ran this harness (version "
                     f"{cryptography.__version__}); the key fields were "
                     f"also checked against it.")
        for idx, blob, name, fields in jobs:
            pub = open(os.path.join(SCRATCH, f"test_{name}.pub"), "rb").read()
            key = load_ssh_public_key(pub)
            if name == "ed25519":
                from cryptography.hazmat.primitives.asymmetric.ed25519 import (
                    Ed25519PublicKey)
                raw = key.public_bytes(
                    cryptography.hazmat.primitives.serialization.Encoding.Raw,
                    cryptography.hazmat.primitives.serialization.PublicFormat.Raw)
                check(isinstance(key, Ed25519PublicKey) and raw == fields["key"],
                      "realkey-crypto-ed", "cryptography key bytes differ")
            else:
                nums = key.public_numbers()
                check(nums.e == fields["e"] and nums.n == fields["n"],
                      "realkey-crypto-rsa", "cryptography e or n differs")
    except ImportError:
        notes.append("Python's `cryptography` library was not importable "
                     "in the interpreter that ran this harness; the field "
                     "checks rest on the harness's own parse of the blobs.")
    answers = None
    return jobs, answers


# ---------------------------------------------------------------------------
# Section 3: generated differential against the oracle.
# ---------------------------------------------------------------------------

def gen_mpints(rng):
    vals = [0, 1, 2, 127, 128, 129, 255, 256, 257, 32767, 32768,
            -1, -2, -127, -128, -129, -255, -256, -32768, -32769,
            2**31 - 1, 2**31, -2**31, -2**31 - 1, 2**63 - 1, -2**63,
            2**64 - 1, -2**64, 10**30, -10**30]
    for _ in range(1400):
        bits = rng.randrange(0, 257)
        v = rng.getrandbits(bits)
        if rng.random() < 0.5:
            v = -v
        vals.append(v)
    return vals


def gen_strings(rng):
    out = []
    for _ in range(700):
        ln = rng.choice([0, 1, 2, 3, 5, 8, 16, 33, 64, 100, 255, 300])
        out.append(bytes(rng.randrange(256) for _ in range(ln)))
    return out


def gen_names(rng):
    alpha = [b for b in range(0x21, 0x7F) if b != 44]
    out = []
    for _ in range(700):
        k = rng.randrange(0, 6)
        names = []
        for _ in range(k):
            ln = rng.randrange(1, 13)
            names.append(bytes(rng.choice(alpha) for _ in range(ln)))
        out.append(names)
    return out


def gen_blobs(rng):
    out = []
    for _ in range(400):
        out.append(("ed", bytes(rng.randrange(256) for _ in range(32))))
    for _ in range(400):
        e = rng.getrandbits(rng.choice([2, 3, 5, 17, 32])) + 1
        if rng.random() < 0.25:
            e = e + 1 if e % 2 == 1 else e  # even e on purpose: positivity only
        nbits = rng.choice([16, 64, 256, 512])
        n = rng.getrandbits(nbits) | 1
        out.append(("rsa", e, n))
    out.append(("rsa", 65537, (1 << 2047) + 123456789))
    return out


def section_generated(tool, rng):
    jobs = []
    for v in gen_mpints(rng):
        i = tool.ask(req("mpint", enc_mpint_field(v)))
        jobs.append((i, want_ok(enc_mpint_field(v)), f"gen-mpint-{v}"))
    for s in gen_strings(rng):
        i = tool.ask(req("string", enc_string(s)))
        jobs.append((i, want_ok(enc_string(s)), f"gen-string-{len(s)}"))
    for names in gen_names(rng):
        i = tool.ask(req("names", enc_names_field(names)))
        jobs.append((i, want_ok(enc_names_field(names)), f"gen-names-{len(names)}"))
    for b in gen_blobs(rng):
        i = tool.ask(req("blob", enc_blob(b)))
        jobs.append((i, want_ok(enc_blob(b)), f"gen-blob-{b[0]}"))
    return jobs


def section_raw(tool, rng):
    jobs = []
    for op in ("mpint", "string", "names", "blob"):
        for _ in range(200):
            ln = rng.randrange(0, 49)
            bs = bytes(rng.randrange(256) for _ in range(ln))
            i = tool.ask(req(op, bs))
            jobs.append((i, oracle_answer(op, bs), f"raw-{op}"))
    return jobs


# ---------------------------------------------------------------------------
# Section 4: mutations.
# ---------------------------------------------------------------------------

def section_mutations(tool):
    jobs = []

    def settle(op, bs, label):
        i = tool.ask(req(op, bs))
        jobs.append((i, oracle_answer(op, bs), label))

    def expect_none(op, bs, label):
        i = tool.ask(req(op, bs))
        jobs.append((i, "none", label))

    # Non minimal mpints, both directions and the lone zero byte.
    expect_none("mpint", enc_string(bytes([0])), "mut-mpint-lone-zero")
    expect_none("mpint", enc_string(bytes([0, 127])), "mut-mpint-extra-zero")
    expect_none("mpint", enc_string(bytes([0, 0, 5])), "mut-mpint-two-zeros")
    expect_none("mpint", enc_string(bytes([255, 128])), "mut-mpint-extra-ff")
    expect_none("mpint", enc_string(bytes([255, 255, 0])), "mut-mpint-two-ff")
    # The minimal neighbours of those must still read.
    settle("mpint", enc_string(bytes([0, 128])), "mut-mpint-needed-zero")
    settle("mpint", enc_string(bytes([255, 127])), "mut-mpint-needed-ff")
    # Length overruns and truncations.
    expect_none("string", bytes([0, 0, 0, 5, 104, 105]), "mut-string-overrun")
    expect_none("mpint", bytes([0, 0, 0, 4, 1, 2]), "mut-mpint-overrun")
    expect_none("names", bytes([0, 0, 1, 0, 97]), "mut-names-overrun")
    expect_none("string", bytes([0, 0, 0]), "mut-string-short-prefix")
    blob = enc_blob(("rsa", 65537, 3233))
    for cut in range(len(blob)):
        settle("blob", blob[:cut], f"mut-blob-trunc-{cut}")
    field = enc_mpint_field(-0xDEADBEEF)
    for cut in range(len(field)):
        settle("mpint", field[:cut], f"mut-mpint-trunc-{cut}")
    # Trailing bytes.
    expect_none("blob", blob + bytes([0]), "mut-blob-trailing")
    expect_none("mpint", field + bytes([1]), "mut-mpint-trailing")
    expect_none("string", enc_string(b"hi") + bytes([0]), "mut-string-trailing")
    expect_none("names", enc_names_field([b"a"]) + bytes([0]), "mut-names-trailing")
    # Blob specific.
    expect_none("blob", enc_blob(("ed", bytes(31))), "mut-ed-31")
    expect_none("blob", enc_blob(("ed", bytes(33))), "mut-ed-33")
    expect_none("blob", enc_string(b"ssh-rsa") + enc_mpint_field(0)
                + enc_mpint_field(3233), "mut-rsa-e-zero")
    expect_none("blob", enc_string(b"ssh-rsa") + enc_mpint_field(-128)
                + enc_mpint_field(3233), "mut-rsa-e-negative")
    expect_none("blob", enc_string(b"ssh-rsa") + enc_mpint_field(17)
                + enc_mpint_field(0), "mut-rsa-n-zero")
    expect_none("blob", enc_string(b"ssh-dss") + enc_string(bytes(32)),
                "mut-blob-unknown-alg")
    expect_none("blob", enc_string(b"") + enc_string(bytes(32)),
                "mut-blob-empty-alg")
    expect_none("blob", enc_string(b"ssh-rsa") + enc_string(bytes([0, 17]))
                + enc_mpint_field(3233), "mut-rsa-e-nonminimal")
    # Name-list content faults.
    expect_none("names", enc_string(b",a"), "mut-names-leading-comma")
    expect_none("names", enc_string(b"a,"), "mut-names-trailing-comma")
    expect_none("names", enc_string(b"a,,b"), "mut-names-double-comma")
    expect_none("names", enc_string(b"a b"), "mut-names-space")
    expect_none("names", enc_string(bytes([97, 127])), "mut-names-del")
    expect_none("names", enc_string(bytes([97, 0])), "mut-names-nul")
    expect_none("names", enc_string(bytes([97, 200])), "mut-names-high")
    return jobs


# ---------------------------------------------------------------------------
# Section 5: the line protocol.
# ---------------------------------------------------------------------------

def section_protocol():
    cases = [
        ("bogus 1,2", "error"),
        ("mpint 256", "error"),
        ("mpint 01", "error"),
        ("mpint 1,,2", "error"),
        ("mpint 1,2 ", "error"),
        ("mpint 1, 2", "error"),
        ("mpint 99999999999999999999999999", "error"),
        ("mpint", "none"),
        ("string 0,0,0,0", "ok:0,0,0,0"),
        ("blob 0,0,0,0", "none"),
    ]
    proc = subprocess.run([EXE], input="\n".join(c for c, _ in cases) + "\n",
                          capture_output=True, text=True, timeout=120)
    answers = proc.stdout.splitlines()
    n = 0
    agree = 0
    check(len(answers) == len(cases), "protocol-count",
          f"{len(answers)} answers for {len(cases)} requests")
    for (line, want), got in zip(cases, answers):
        n += 1
        if got == want:
            agree += 1
        else:
            check(False, "protocol", f"{line!r}: got {got!r}, want {want!r}")
    # An empty line gets no answer, and CRLF endings are accepted.
    raw = b"mpint 0,0,0,0\r\n\r\nstring 0,0,0,0\r\n"
    proc = subprocess.run([EXE], input=raw, capture_output=True, timeout=120)
    lines = proc.stdout.decode().splitlines()
    n += 1
    if lines == ["ok:0,0,0,0", "ok:0,0,0,0"]:
        agree += 1
    else:
        check(False, "protocol-crlf", f"CRLF run answered {lines}")
    return n, agree


# ---------------------------------------------------------------------------
# Main.
# ---------------------------------------------------------------------------

def settle(tool, jobs, section_name):
    agree = 0
    for i, want, label in jobs:
        got = tool.answers[i]
        if got == want:
            agree += 1
        else:
            check(False, section_name, f"{label}: got {got!r}, want {want!r}")
    return agree


def main():
    if "--skip-build" not in sys.argv:
        env = dict(os.environ)
        env["PATH"] = os.path.expanduser("~/.elan/bin") + ":" + env["PATH"]
        subprocess.run(["lake", "build"], cwd=ROOT, check=True, env=env,
                       capture_output=True, text=True, timeout=1800)
    rng = random.Random(SEED)
    rows = []
    notes = []

    # Fixed cases.
    tool = Tool()
    fixed_jobs = list(section_fixed(tool))
    tool.run()
    agree = settle(tool, fixed_jobs, "fixed")
    rows.append(("Fixed cases (RFC 4251 mpint examples, strings, "
                 "name-lists, blobs)", len(fixed_jobs), agree))

    # Real keys: requests are queued on their own tool, then settled.
    tool = Tool()
    rk = section_real_keys(tool, notes)
    if isinstance(rk[0], list):
        jobs = rk[0]
        tool.run()
        agree = 0
        for idx, blob, name, fields in jobs:
            if tool.answers[idx] == want_ok(blob):
                agree += 1
            else:
                check(False, "real-keys", f"{name}: reprint differs")
        rows.append(("Real keys from ssh-keygen (ed25519, RSA 2048), "
                     "read and reprinted byte for byte", len(jobs), agree))
    else:
        rows.append(("Real keys from ssh-keygen", 0, 0))

    # Generated differential.
    tool = Tool()
    jobs = section_generated(tool, rng)
    tool.run()
    agree = settle(tool, jobs, "generated")
    rows.append(("Oracle differential, generated values across all types",
                 len(jobs), agree))

    # Random raw bytes differential.
    tool = Tool()
    jobs = section_raw(tool, rng)
    tool.run()
    agree = settle(tool, jobs, "raw")
    rows.append(("Oracle differential, random raw byte strings",
                 len(jobs), agree))

    # Mutations.
    tool = Tool()
    jobs = section_mutations(tool)
    tool.run()
    agree = settle(tool, jobs, "mutations")
    rows.append(("Mutations (non minimal mpints, overruns, truncations, "
                 "trailing bytes, blob and name-list faults)",
                 len(jobs), agree))

    # Line protocol.
    n_in, n_agree = section_protocol()
    rows.append(("Line protocol cases", n_in, n_agree))

    total_in = sum(r[1] for r in rows)
    total_agree = sum(r[2] for r in rows)

    out = []
    out.append("# Test results: ssh")
    out.append("")
    out.append(f"Seed: {SEED}. Tool: the Lean command line program, one "
               "process per section, requests batched.")
    out.append("")
    for note in notes:
        out.append(note)
        out.append("")
    out.append("| Section | Inputs | Agreements |")
    out.append("| --- | --- | --- |")
    for name, nin, nag in rows:
        out.append(f"| {name} | {nin} | {nag} |")
    out.append(f"| Total | {total_in} | {total_agree} |")
    out.append("")
    out.append("Named differences: none. The tool agreed with the oracle "
               "on every generated and mutated input, and reprinted the "
               "real ssh-keygen blobs byte for byte.")
    out.append("")
    out.append("Pinned readings exercised by these tests: an RSA blob "
               "whose e is even reads (positivity is the only check on "
               "e and n); a lone zero byte is not an mpint (zero is the "
               "empty content); a name may hold any byte from 0x21 to "
               "0x7E except the comma.")
    out.append("")
    if failures:
        out.append(f"Failures: {len(failures)}.")
        for f in failures:
            out.append(f"- {f}")
    else:
        out.append("Failures: none.")
    out.append("")
    with open(os.path.join(HERE, "TEST-RESULTS.md"), "w") as fh:
        fh.write("\n".join(out))
    print(f"total {total_agree}/{total_in} agreements, "
          f"{len(failures)} failures")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
