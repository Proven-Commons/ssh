# SSH wire types: specification

This is the specification of the first slice for the `ssh`
package: the SSH binary packet types of RFC 4251 section 5 and
the public key blobs of RFC 4253 section 6.6, in Lean, with the
round trips proved. The formats themselves are defined by
those RFCs; this file states what the slice does with them,
and the exact readings it pins where the RFC leaves room.

What the slice is: a reader and a writer for the primitive
types (byte, boolean, uint32, uint64, string, name-list, mpint)
and for public key blobs of two algorithms. What it is not:
signatures, key exchange, certificates, or any other algorithm.
Nothing here checks that a key is a good key (for example that
an RSA modulus is the product of two primes); the slice reads
and writes the wire forms only.

All values are held as lists of bytes (`List UInt8`). A reader
takes bytes and returns the value and the bytes left over, or
fails. A writer takes a value and returns bytes.

## byte

One byte. The reader takes the first byte; on empty input it
fails. Writing then reading returns the byte and the rest.

## boolean

One byte. The writer writes 0 for false and 1 for true, and
never any other byte. The reader reads the byte 0 as false and
any nonzero byte as true (RFC 4251: "any non-zero byte is
true").

Because the writer only writes 0 and 1, a written boolean reads
back exactly. The other direction is not exact, and this is a
pinned reading of the slice: reading the byte 7 gives true,
and writing that true gives the byte 1, so the reprint of a
read boolean can differ from the bytes that were read. The
round trip theorem is stated and proved for the write then
read direction only.

## uint32 and uint64

Four (or eight) bytes, big endian: the first byte is the most
significant. Reading fewer bytes than the width fails. Writing
then reading returns the number and the rest, for any number
below 2^32 (or 2^64).

## string

A uint32 length, then that many bytes. A length that runs past
the end of the input fails: the reader never invents bytes.
Writing then reading returns the content and the rest, for any
content shorter than 2^32 bytes.

## name-list

A string whose content is names joined by single comma bytes
(the byte 44). The value is a list of names, and each name is a
list of bytes.

The name rule of this slice: a name is nonempty, and every
byte of a name lies from 0x21 to 0x7E and is not the comma
byte. (RFC 4251 says names use US-ASCII letters, digits, and
characters such as `@`, `.`, `_`, `-`; this slice accepts the
whole printable range the section works in, 0x21 to 0x7E, apart
from the comma that parts the names. That is the exact rule;
no other byte is accepted in a name.)

The empty content is the empty list of names. A content with
an empty name in it fails: a leading comma, a trailing comma,
or two commas in a row all fail, and so does a name holding a
byte outside the rule above. Writing a list of names that all
follow the rule, then reading, returns the same list and the
rest, when the joined content is shorter than 2^32 bytes.

## mpint

The value is a Lean `Int`. The wire form is a string (a uint32
length, then content bytes) holding the value in two's
complement big endian form, in the smallest number of bytes:

- Zero is the empty content.
- A positive value is its big endian bytes, with one leading
  0x00 byte exactly when the value's own first byte would have
  its high bit (128) set.
- A negative value is its two's complement bytes, with no
  leading byte that could be dropped: a leading 0xFF byte is
  present exactly when the next byte's high bit is clear.

The reader computes the value from the content (empty content
is 0) and checks the minimal form. The reader fails when the
content is not minimal, in exactly these cases:

- the content is a single byte 0x00 (zero must be empty), or
- the first byte is 0x00 and the second byte's high bit is
  clear (the zero byte could be dropped), or
- the first byte is 0xFF and the second byte's high bit is set
  (the 0xFF byte could be dropped).

The writer always produces the minimal form. It is proved
that reading the writer's content gives the value back, for
every `Int`, and that the writer's content always passes the
minimal form check.

## Public key blobs (RFC 4253 section 6.6)

A blob is read from bytes that the blob must consume exactly:
anything left over after the blob fails the read. A blob
starts with a string, the algorithm name. Two algorithm names
are read in this slice; any other name fails.

### ssh-ed25519

After the name, one string, the public key. The key is exactly
32 bytes (RFC 4253 fixes the length); a key string of any other
length fails.

### ssh-rsa

After the name, two mpints: `e` then `n`. This slice's reading:
`e` and `n` must both be positive; zero or negative fails. (The
wire form can carry zero or negative mpints; a key with such
an `e` or `n` is not a key.) The RFC does not require `e` to be
odd in the blob format, and this slice does not check oddness;
positivity is the only check. The mpints inside the blob follow
the mpint rules above, so a non minimal mpint fails the blob
too.

Writing a blob writes the name as a string, then the fields,
with the mpints in minimal form. It is proved that reading a
written blob gives the blob back, for any blob that is well
formed: an ed25519 key of exactly 32 bytes, or an RSA pair with
`e` and `n` positive and their mpint contents shorter than
2^32 bytes.

## The command line protocol

The tool in `Main.lean` answers one request per line. A
request is an operation name and a payload, parted by one
space; a request with no payload has no trailing space. The
payload is the bytes of the input as decimal numbers from 0 to
255, parted by commas, with no spaces. A number is plain
decimal: no sign, no leading zeros (the number 0 itself is
written `0`), and at most twenty digits. An empty line gets no
answer. A request that breaks this shape (an unknown operation,
a number over 255, a bad number, extra spaces) is answered
`error`.

The operations:

- `mpint`: the payload is the bytes of exactly one mpint field
  (the length prefix and the content, and nothing after). The
  answer is `ok:` and the canonical field bytes (the field
  reprinted from the value read, which is always in minimal
  form), or `none` when the field is turned away.
- `string`: the same shape for exactly one string field.
- `names`: the same shape for exactly one name-list field.
- `blob`: the payload is the bytes of one whole key blob. The
  answer is `ok:` and the canonical blob bytes, or `none` when
  the blob is turned away.

The answer bytes are printed in the same decimal comma form as
the payload. In every operation the input must be consumed
exactly: trailing bytes turn the answer to `none`.

## Properties and their theorems

Each property a reader can check in the page (`README.md`)
names its theorem. The theorems are stated in `Spec.lean`
and proved in `Proofs/SpecProofs.lean`. The refusal theorems
are single inputs, one for each named rejection case in the
test harness; the tests in `tests/` cover each rule on many
more inputs.

| Property | Theorem |
|----------|---------|
| Reading a written byte gives the byte and the rest back | `Spec.readByte_writeByte` |
| Reading a written boolean gives the boolean and the rest back | `Spec.readBool_writeBool` |
| Reading a written uint32 gives the number back, below 2^32 | `Spec.readUInt32_writeUInt32` |
| Reading a written uint64 gives the number back, below 2^64 | `Spec.readUInt64_writeUInt64` |
| Reading a written string gives the content back, for content shorter than 2^32 bytes | `Spec.readString_writeString` |
| Reading a written name-list gives the list back, when every name follows the name rule and the joined content is shorter than 2^32 bytes | `Spec.readNames_writeNames` |
| The value of the mpint writer's content is the integer itself, for every integer | `Spec.mpintValue_mpintBytes` |
| The mpint writer's content always passes the minimal form check, for every integer | `Spec.mpintMinimal_mpintBytes` |
| Reading a written mpint field gives the integer back, when the content is shorter than 2^32 bytes | `Spec.readMpint_writeMpint` |
| Reading a written key blob gives the blob back, for every well formed blob | `Spec.readBlob_writeBlob` |
| Zero is written as the empty content | `Spec.mpint_zero_write` |
| Reading the zero field gives zero | `Spec.mpint_zero_read` |
| The RFC's large positive example, written as the RFC prints it | `Spec.mpint_big_write` |
| The RFC's large positive example, read | `Spec.mpint_big_read` |
| The value 0x80 is written with a leading zero byte | `Spec.mpint_80_write` |
| Reading the 0x80 field gives 0x80 | `Spec.mpint_80_read` |
| The RFC's small negative example, written | `Spec.mpint_neg_small_write` |
| The RFC's small negative example, read | `Spec.mpint_neg_small_read` |
| The RFC's large negative example, written | `Spec.mpint_neg_big_write` |
| The RFC's large negative example, read | `Spec.mpint_neg_big_read` |
| A read of the byte 7 as a boolean gives true | `Spec.bool_seven_reads_true` |
| True writes as the byte 1 | `Spec.bool_true_writes_one` |
| A string field holding "hi" reads back as "hi" | `Spec.string_round` |
| A name-list field holding "a" and "bc" reads back as those names | `Spec.names_round` |
| The empty string content is the empty list of names | `Spec.names_empty` |
| An ed25519 blob with a fixed pattern key, written and read back | `Spec.blob_ed25519_round` |
| A small RSA blob (modulus 3233, exponent 17), written and read back | `Spec.blob_rsa_round` |
| A lone zero byte as mpint content is refused | `Spec.mpint_lone_zero_rejected` |
| An mpint content with a droppable leading zero byte is refused | `Spec.mpint_extra_zero_rejected` |
| An mpint content with a droppable leading 255 byte is refused | `Spec.mpint_extra_ff_rejected` |
| An mpint field cut short by its length is refused | `Spec.mpint_truncated_rejected` |
| A string field whose length runs past the input is refused | `Spec.string_length_overrun_rejected` |
| A name holding a byte outside the name rule is refused | `Spec.names_bad_byte_rejected` |
| A name-list whose content is a single comma is refused | `Spec.names_comma_rejected` |
| An ed25519 key string of 31 bytes is refused | `Spec.blob_ed25519_short_key_rejected` |
| A blob whose key length runs past the input is refused | `Spec.blob_length_overrun_rejected` |
| A blob naming an unread algorithm is refused | `Spec.blob_unknown_alg_rejected` |
