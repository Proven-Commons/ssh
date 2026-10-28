# ssh: SSH wire types and key blobs, with proved round trips

The SSH primitive data types of RFC 4251 section 5 (byte, boolean, uint32, uint64, string, name-list, mpint) and the public key blobs of RFC 4253 section 6.6 for two algorithms (ssh-ed25519 and ssh-rsa), in Lean. Each type has a reader and a writer, and the round trips are proved, including the mpint round trip for every integer and the blob round trips. The tests run the tool against real keys made by `ssh-keygen` and against a strict oracle written from the two RFCs; see `tests/TEST-RESULTS.md` for the counts.

Status: in progress. The specification has not yet been approved by a reviewer apart from its author, and no statement file (`Spec.lean`) has been added by a reviewer, so this is not verified.

## What is proved

The definitions are in `Ssh/Value.lean` (the writers, the name rule, the mpint encodings, the blob type and its well-formedness rules) and `Ssh/Parse.lean` (the readers, the mpint value and minimal form check). The proofs are in `Proofs/RoundTrip.lean`, and worked examples (the mpint examples printed in RFC 4251 section 5, byte for byte, and blob examples) are proved in `Proofs/Examples.lean`.

| Claim | Theorem |
|-------|---------|
| Reading a written byte gives the byte back (any rest). | `Ssh.Proofs.readByte_writeByte` |
| Reading a written boolean gives the boolean back (any rest). The writer writes only 0 and 1; a read of any nonzero byte gives true, so the other direction is not a round trip. | `Ssh.Proofs.readBool_writeBool` |
| Reading a written uint32 gives the number back (any rest), for numbers below 2^32. | `Ssh.Proofs.readUInt32_writeUInt32` |
| Reading a written uint64 gives the number back (any rest), for numbers below 2^64. | `Ssh.Proofs.readUInt64_writeUInt64` |
| Reading a written string gives the content back (any rest), for content shorter than 2^32 bytes. | `Ssh.Proofs.readString_writeString` |
| Reading a written name-list gives the list back (any rest), when every name follows the name rule and the joined content is shorter than 2^32 bytes. | `Ssh.Proofs.readNames_writeNames` |
| The value read from the bytes the mpint writer produces is the integer itself, for every integer. | `Ssh.Proofs.mpintValue_mpintBytes` |
| The mpint writer's content always passes the minimal form check, for every integer. | `Ssh.Proofs.mpintMinimal_mpintBytes` |
| Reading a written mpint field gives the integer back (any rest), when the content is shorter than 2^32 bytes. | `Ssh.Proofs.readMpint_writeMpint` |
| Reading a written key blob gives the blob back, for every well formed blob (32 byte ed25519 key; RSA with positive `e` and `n` whose mpint contents are shorter than 2^32 bytes). | `Ssh.Proofs.readBlob_writeBlob` |

The headline claims check against the standard axioms only (`propext`, `Classical.choice`, `Quot.sound`), or no axioms at all, which a reader can confirm with `#print axioms` on the names above, or by running `lake env lean Ssh/Verify.lean`.

The command-line tool in `Main.lean` calls these functions directly.

## What is not proved

- That the readers accept every byte string the RFCs allow, and reject every one they forbid. The round trips do not need either, so neither is proved. The oracle differential and the mutation tests check that behaviour instead, and the results file records the outcome.
- That a key blob holds a good key. An ed25519 key is any 32 bytes; an RSA pair is any two positive integers. Nothing checks that a modulus is a product of primes, that an exponent suits the modulus, or that a key was ever generated properly.
- Anything about signatures, key exchange, certificates, or algorithms other than ssh-ed25519 and ssh-rsa. Other algorithm names are turned away.
- Reading requests and printing answers in `Main.lean`: splitting lines, and the decimal number reader. The tests cover them, malformed requests included.
- Speed. The code works on lists of bytes, which suits proofs, not large data.

## What you must trust

- The Lean kernel, which checks the proofs.
- The Lean compiler, with the C compiler and linker shipped with it, and the runtime, which turn the proved definitions into the program that runs.
- Lean's core library, including the compiled code it puts in place of some definitions the proofs reason about.
- The operating system and hardware it runs on.
- The strict oracle in the test harness, written from RFC 4251 and RFC 4253, and the `ssh-keygen` program that made the real test keys. The results file records what was used and what was not available.

This project has no dependencies beyond Lean itself.

## Run it

Needs Linux and [elan](https://github.com/leanprover/elan). Build, then feed request lines to the tool:

```
lake build
echo "mpint 0,0,0,2,237,204" | .lake/build/bin/ssh
```

That request is the mpint field for the value -4660 (the RFC's own example), and the answer is `ok:0,0,0,2,237,204`: the value read back and reprinted in its canonical (minimal) form. Bytes the reader turns away, such as the non minimal field `0,0,0,1,0` (a lone zero byte), answer `none`. A malformed request answers `error`. See `SPEC.md` for the full protocol.

## Re-check it

Needs Linux, elan, and Python 3.

```
lake build
grep -rn "sorry" --include="*.lean" Ssh Proofs Main.lean Ssh.lean Proofs.lean
python3 tests/run_tests.py
```

The grep should print nothing: there is no `sorry` anywhere. The test script rebuilds the tool, runs the RFC's fixed mpint examples, the real key cases when `ssh-keygen` is on the machine (it says so in the results file when it is not), the differential against the strict oracle, and the mutation cases, and writes the counts to `tests/TEST-RESULTS.md`.
