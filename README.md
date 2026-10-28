# ssh: SSH wire types and key blobs, with proved round trips

Status: in-progress

The SSH primitive data types of RFC 4251 section 5 (byte,
boolean, uint32, uint64, string, name-list, mpint) and the
public key blobs of RFC 4253 section 6.6 for two algorithms
(ssh-ed25519 and ssh-rsa), in Lean. Each type has a reader
and a writer, and the round trips are proved, including the
mpint round trip for every integer and the blob round trips.
The definitions are in `Ssh/Value.lean` (the writers, the
name rule, the mpint encodings, the blob type and its
well-formedness rules) and `Ssh/Parse.lean` (the readers,
the mpint value and minimal form check). The rules are
written out in `SPEC.md`. The tests run the tool against
real keys made by `ssh-keygen` and against a strict oracle
written from the two RFCs; see `tests/TEST-RESULTS.md` for
the counts.

The statements a reviewer approves are in `Spec.lean`,
with their proofs in `Proofs/SpecProofs.lean`. No reviewer
has approved them yet, so this project is not called
verified.

## How to run it

`lake build` builds the library, the proofs, and the
command line tool. The tool reads one request per line:
an operation name, a space, and the field bytes as
comma-separated decimal byte codes. It answers `ok:` and
the canonical reprint when the field reads, `none` when
the field is turned away, and `error` when the request
itself is malformed.

```
lake build
echo "mpint 0,0,0,2,237,204" | .lake/build/bin/ssh
```

That request is the mpint field for the value -4660 (the
RFC's own example), and the answer is `ok:0,0,0,2,237,204`:
the value read back and reprinted in its canonical
(minimal) form. Bytes the reader turns away, such as the
non minimal field `0,0,0,1,0` (a lone zero byte), answer
`none`. A malformed request answers `error`. See `SPEC.md`
for the full protocol.

`python3 tests/run_tests.py` rebuilds the tool, runs the
RFC's fixed mpint examples, the real key cases when
`ssh-keygen` is on the machine (it says so in the results
file when it is not), the differential against the strict
oracle, and the mutation cases, and writes the counts to
`tests/TEST-RESULTS.md`.

## What is proved

Each claim below names the theorem behind it. The
theorems are stated in `Spec.lean` (the challenge file,
where they end in `sorry`) and proved in
`Proofs/SpecProofs.lean`, under the same names.
`comparator.json` lists all of them.

| Claim | Theorem |
|-------|---------|
| Reading a written byte gives the byte back (any rest). | `Spec.readByte_writeByte` |
| Reading a written boolean gives the boolean back (any rest). The writer writes only 0 and 1; a read of any nonzero byte gives true, so the other direction is not a round trip. | `Spec.readBool_writeBool` |
| Reading a written uint32 gives the number back (any rest), for numbers below 2^32. | `Spec.readUInt32_writeUInt32` |
| Reading a written uint64 gives the number back (any rest), for numbers below 2^64. | `Spec.readUInt64_writeUInt64` |
| Reading a written string gives the content back (any rest), for content shorter than 2^32 bytes. | `Spec.readString_writeString` |
| Reading a written name-list gives the list back (any rest), when every name follows the name rule and the joined content is shorter than 2^32 bytes. | `Spec.readNames_writeNames` |
| The value read from the bytes the mpint writer produces is the integer itself, for every integer. | `Spec.mpintValue_mpintBytes` |
| The mpint writer's content always passes the minimal form check, for every integer. | `Spec.mpintMinimal_mpintBytes` |
| Reading a written mpint field gives the integer back (any rest), when the content is shorter than 2^32 bytes. | `Spec.readMpint_writeMpint` |
| Reading a written key blob gives the blob back, for every well formed blob (32 byte ed25519 key; RSA with positive `e` and `n` whose mpint contents are shorter than 2^32 bytes). | `Spec.readBlob_writeBlob` |
| Zero is written as the empty content: the field is four zero bytes. | `Spec.mpint_zero_write` |
| Reading the zero field gives zero. | `Spec.mpint_zero_read` |
| The RFC's large positive example (0x9a378f9b2e332a7), written byte for byte as RFC 4251 section 5 prints it. | `Spec.mpint_big_write` |
| The RFC's large positive example, read back to the value. | `Spec.mpint_big_read` |
| The value 0x80 is written with a leading zero byte: the field is `0, 0, 0, 2, 0, 128`. | `Spec.mpint_80_write` |
| Reading the 0x80 field gives 0x80. | `Spec.mpint_80_read` |
| The RFC's small negative example (-0x1234), written. | `Spec.mpint_neg_small_write` |
| The RFC's small negative example, read. | `Spec.mpint_neg_small_read` |
| The RFC's large negative example (-0xdeadbeef), written. | `Spec.mpint_neg_big_write` |
| The RFC's large negative example, read. | `Spec.mpint_neg_big_read` |
| A read of the byte 7 as a boolean gives true: any nonzero byte is true. | `Spec.bool_seven_reads_true` |
| True writes as the byte 1. | `Spec.bool_true_writes_one` |
| A string field holding "hi" reads back as "hi". | `Spec.string_round` |
| A name-list field holding the names "a" and "bc" reads back as those names. | `Spec.names_round` |
| The empty string content is the empty list of names. | `Spec.names_empty` |
| An ed25519 blob with a fixed pattern key (the bytes 0 to 31), written and read back. | `Spec.blob_ed25519_round` |
| A small RSA blob (modulus 3233, exponent 17), written and read back. | `Spec.blob_rsa_round` |
| A lone zero byte as mpint content is refused: zero is the empty content. | `Spec.mpint_lone_zero_rejected` |
| An mpint content with a leading zero byte that could be dropped is refused. | `Spec.mpint_extra_zero_rejected` |
| An mpint content with a leading 255 byte that could be dropped is refused. | `Spec.mpint_extra_ff_rejected` |
| An mpint field whose length says two content bytes but only one follows is refused. | `Spec.mpint_truncated_rejected` |
| A string field whose length says five bytes but only two follow is refused. | `Spec.string_length_overrun_rejected` |
| A name holding a byte outside the name rule (here the byte 1) is refused. | `Spec.names_bad_byte_rejected` |
| A name-list whose content is a single comma, holding two empty names, is refused. | `Spec.names_comma_rejected` |
| An ed25519 key string of 31 bytes is refused: the key is exactly 32 bytes. | `Spec.blob_ed25519_short_key_rejected` |
| A blob whose key length field says 40 bytes but only 32 follow is refused. | `Spec.blob_length_overrun_rejected` |
| A blob naming an algorithm this slice does not read (here ssh-dss) is refused. | `Spec.blob_unknown_alg_rejected` |

The round trip theorems rest on the proofs in
`Proofs/RoundTrip.lean`, where they are
`Ssh.Proofs.readByte_writeByte` and its companions, and
the worked examples and most refusals rest on
`Proofs/Examples.lean`, where they are the
`Ssh.Examples` theorems of the same names. The statements
check against the standard axioms only (`propext`,
`Classical.choice`, `Quot.sound`), or no axioms at all,
which a reader can confirm with `#print axioms` on the
names in the table in their `Ssh.Proofs` and
`Ssh.Examples` forms, or by running
`lake env lean Ssh/Verify.lean`. The remaining single
inputs (the 0x80 example and the overrun and bad name
refusals) are checked in the kernel with `decide +kernel`.

The command-line tool in `Main.lean` calls these
functions directly: the field readers and `readBlob` on
the way in, and the writers on the way out.

## What is not proved

- That the readers accept every byte string the RFCs
  allow, and reject every one they forbid. The round trips
  do not need either, so neither is proved. The refusal
  theorems pin single inputs only. The oracle differential
  and the mutation tests check that behaviour instead, and
  the results file records the outcome.
- That a key blob holds a good key. The key formats are
  exercised as blobs: an ed25519 key is any 32 bytes; an
  RSA pair is any two positive integers. Nothing checks
  that a modulus is a product of primes, that an exponent
  suits the modulus, or that a key was ever generated
  properly. No key semantics are proved.
- Anything about signatures, key exchange, certificates,
  or algorithms other than ssh-ed25519 and ssh-rsa. Other
  algorithm names are turned away, and one such refusal is
  pinned above; the general case rests on the tests.
- Reading requests and printing answers in `Main.lean`:
  splitting lines, and the decimal number reader. The
  tests cover them, malformed requests included.
- Speed. The code works on lists of bytes, which suits
  proofs, not large data.

## What you must trust

- The Lean kernel (Lean 4.35.0, pinned in
  `lean-toolchain`), which checks every proof.
- The Lean compiler, with the C compiler and linker
  shipped with it, which turns the proved definitions into
  the program that runs.
- The Lean runtime, which runs that program.
- The hardware the program runs on.
- Every dependency in `lake-manifest.json`: the manifest
  lists no packages, so there are no library dependencies
  to trust beyond the Lean toolchain itself.
- Lean's core library, including the compiled code it puts
  in place of some definitions the proofs reason about.
- The operating system the program runs on.
- That `SPEC.md` states the reading of RFC 4251 and
  RFC 4253 you intend. The proofs are about the readers
  and writers in this repo following each other exactly;
  the fidelity of the spec to the RFCs is a reading,
  pinned in `SPEC.md` where an RFC leaves a choice open.
- The strict oracle in the test harness, written from
  RFC 4251 and RFC 4253, and the `ssh-keygen` program
  that made the real test keys. Python's `cryptography`
  library was not importable in the environment that ran
  the harness, so no library cross-check of the blobs ran;
  the field checks rest on the harness's own parse of the
  blobs and on the real keys. The results file records
  what was used and what was not available.
- The line handling in `Main.lean` (splitting a request
  line, reading decimal codes). The tests drive it, and no
  proof covers it.
- There are no exceptions to item 4 of the bar: the
  project uses none of the features it forbids.

## Re-check it

1. `lake comparator --paranoid`: builds the challenge
   file `Spec.lean` and the proofs in a sandbox and
   checks that each theorem named in `comparator.json`
   proves exactly the statement in the challenge file,
   uses no axiom but the three standard ones, and is
   accepted by Lean's kernel and every other kernel
   shipped with Lean.
2. `python3 tests/run_tests.py`: the fixed cases, the
   real key cases when `ssh-keygen` is available, the
   differential against the strict oracle, and the
   mutation cases, with counts and any failures written
   to `tests/TEST-RESULTS.md`.
3. `lake build`: the library, the proofs, and the tool
   build clean, and `lake env lean Ssh/Verify.lean`
   prints the axiom list for the headline theorems.
4. Read `SPEC.md` against RFC 4251 section 5 and
   RFC 4253 section 6.6 and check the pinned readings are
   the ones you want.
