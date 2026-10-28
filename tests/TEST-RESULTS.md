# Test results: ssh

Seed: 20261027. Tool: the Lean command line program, one process per section, requests batched.

ssh-keygen was found at /usr/bin/ssh-keygen; it generated fresh test keys (ed25519 and RSA 2048) in the work dir scratch folder for this run. The keys are kept only there and are not committed.

Python's `cryptography` library was not importable in the interpreter that ran this harness; the field checks rest on the harness's own parse of the blobs.

| Section | Inputs | Agreements |
| --- | --- | --- |
| Fixed cases (RFC 4251 mpint examples, strings, name-lists, blobs) | 14 | 14 |
| Real keys from ssh-keygen (ed25519, RSA 2048), read and reprinted byte for byte | 2 | 2 |
| Oracle differential, generated values across all types | 3631 | 3631 |
| Oracle differential, random raw byte strings | 800 | 800 |
| Mutations (non minimal mpints, overruns, truncations, trailing bytes, blob and name-list faults) | 63 | 63 |
| Line protocol cases | 11 | 11 |
| Total | 4521 | 4521 |

Named differences: none. The tool agreed with the oracle on every generated and mutated input, and reprinted the real ssh-keygen blobs byte for byte.

Pinned readings exercised by these tests: an RSA blob whose e is even reads (positivity is the only check on e and n); a lone zero byte is not an mpint (zero is the empty content); a name may hold any byte from 0x21 to 0x7E except the comma.

Failures: none.
