/-
  The specification as Lean statements: the challenge file.

  A reviewer who did not write this file approves it, and `bar.toml`
  records the SHA-256 it had then. The proofs live in `Proofs`
  (`Proofs/SpecProofs.lean`); `lake comparator` checks that each one
  proves exactly the statement written here. The `sorry` below is
  expected in this file only.

  The statements use only the definitions in `Ssh/Value.lean` and
  `Ssh/Parse.lean`, the code under proof named in `bar.toml`. No
  definition of their own is needed, so this project has no
  `Spec/Defs.lean`.
-/

import Ssh

open Ssh

/-! ## The round trips

The statements the slice stands on. Each one is the statement of
the proved theorem of the same shape in `Proofs/RoundTrip.lean`. -/

/-- Reading a written byte gives the byte and the rest back. -/
theorem Spec.readByte_writeByte (b : UInt8) (rest : List UInt8) :
    readByte (writeByte b ++ rest) = some (b, rest) := sorry

/-- Reading a written boolean gives the boolean and the rest
    back. The writer writes only 0 and 1; a read of any nonzero
    byte gives true, so the other direction is not a round
    trip. -/
theorem Spec.readBool_writeBool (b : Bool) (rest : List UInt8) :
    readBool (writeBool b ++ rest) = some (b, rest) := sorry

/-- Reading a written uint32 gives the number and the rest
    back, for every number below 2^32. -/
theorem Spec.readUInt32_writeUInt32 (n : Nat) (rest : List UInt8)
    (h : n < 2 ^ 32) :
    readUInt32 (writeUInt32 n ++ rest) = some (n, rest) := sorry

/-- Reading a written uint64 gives the number and the rest
    back, for every number below 2^64. -/
theorem Spec.readUInt64_writeUInt64 (n : Nat) (rest : List UInt8)
    (h : n < 2 ^ 64) :
    readUInt64 (writeUInt64 n ++ rest) = some (n, rest) := sorry

/-- Reading a written string gives the content and the rest
    back, for content shorter than 2^32 bytes. So a writer that
    wrote nothing, or wrote something shorter, fails this
    statement. -/
theorem Spec.readString_writeString (bs rest : List UInt8)
    (h : bs.length < 2 ^ 32) :
    readString (writeString bs ++ rest) = some (bs, rest) := sorry

/-- Reading a written name-list gives the list and the rest
    back, when every name follows the name rule and the joined
    content is shorter than 2^32 bytes. -/
theorem Spec.readNames_writeNames (names : List (List UInt8))
    (rest : List UInt8)
    (hvalid : ∀ n ∈ names, validName n = true)
    (hlen : (namesContent names).length < 2 ^ 32) :
    readNames (writeNames names ++ rest) = some (names, rest) :=
  sorry

/-- The value read from the content bytes the mpint writer
    produces is the integer itself, for every integer. -/
theorem Spec.mpintValue_mpintBytes (v : Int) :
    mpintValue (mpintBytes v) = v := sorry

/-- The mpint writer's content always passes the minimal form
    check, for every integer. -/
theorem Spec.mpintMinimal_mpintBytes (v : Int) :
    mpintMinimal (mpintBytes v) = true := sorry

/-- Reading a written mpint field gives the integer and the
    rest back, when the content is shorter than 2^32 bytes. -/
theorem Spec.readMpint_writeMpint (v : Int) (rest : List UInt8)
    (h : (mpintBytes v).length < 2 ^ 32) :
    readMpint (writeMpint v ++ rest) = some (v, rest) := sorry

/-- Reading a written key blob gives the blob back, for every
    well formed blob: an ed25519 key of exactly 32 bytes, or an
    RSA pair with positive `e` and `n` whose mpint contents are
    shorter than 2^32 bytes. -/
theorem Spec.readBlob_writeBlob (b : KeyBlob) (hb : blobWF b) :
    readBlob (writeBlob b) = some b := sorry

/-! ## The mpint examples of RFC 4251 section 5

The examples printed in the RFC, byte for byte, on the writing
side and on the reading side. The differential tests run these
through the tool as well; these statements pin them in the
specification. -/

/-- Zero is the empty content. -/
theorem Spec.mpint_zero_write :
    writeMpint 0 = [0, 0, 0, 0] := sorry

/-- Reading the zero field gives zero. -/
theorem Spec.mpint_zero_read :
    parseMpintField [0, 0, 0, 0] = some 0 := sorry

/-- The RFC's large positive example, written. -/
theorem Spec.mpint_big_write :
    writeMpint 0x9a378f9b2e332a7 =
      [0, 0, 0, 8, 9, 163, 120, 249, 178, 227, 50, 167] := sorry

/-- The RFC's large positive example, read. -/
theorem Spec.mpint_big_read :
    parseMpintField [0, 0, 0, 8, 9, 163, 120, 249, 178, 227, 50, 167] =
      some 0x9a378f9b2e332a7 := sorry

/-- The value 0x80 needs a leading zero byte, because its own
    first byte would have the high bit set. Written. -/
theorem Spec.mpint_80_write :
    writeMpint 0x80 = [0, 0, 0, 2, 0, 128] := sorry

/-- The value 0x80, read. -/
theorem Spec.mpint_80_read :
    parseMpintField [0, 0, 0, 2, 0, 128] = some 0x80 := sorry

/-- The RFC's small negative example, -0x1234, written. -/
theorem Spec.mpint_neg_small_write :
    writeMpint (-0x1234) = [0, 0, 0, 2, 237, 204] := sorry

/-- The RFC's small negative example, -0x1234, read. -/
theorem Spec.mpint_neg_small_read :
    parseMpintField [0, 0, 0, 2, 237, 204] = some (-0x1234) := sorry

/-- The RFC's large negative example, -0xdeadbeef, written. -/
theorem Spec.mpint_neg_big_write :
    writeMpint (-0xdeadbeef) = [0, 0, 0, 5, 255, 33, 82, 65, 17] :=
  sorry

/-- The RFC's large negative example, -0xdeadbeef, read. -/
theorem Spec.mpint_neg_big_read :
    parseMpintField [0, 0, 0, 5, 255, 33, 82, 65, 17] =
      some (-0xdeadbeef) := sorry

/-! ## Worked examples

Single cases from `Proofs/Examples.lean`, pinned here so the
page's worked claims name their theorems. -/

/-- A read of the byte 7 as a boolean gives true: any nonzero
    byte is true. -/
theorem Spec.bool_seven_reads_true :
    readBool [7] = some (true, []) := sorry

/-- True writes as the byte 1. -/
theorem Spec.bool_true_writes_one :
    writeBool true = [1] := sorry

/-- A string field holding "hi" reads back as "hi". -/
theorem Spec.string_round :
    parseStringField (writeString [104, 105]) = some [104, 105] :=
  sorry

/-- A name-list field holding the names "a" and "bc" reads
    back as those names. -/
theorem Spec.names_round :
    parseNamesField (writeNames [[97], [98, 99]]) =
      some [[97], [98, 99]] := sorry

/-- The empty string content is the empty list of names. -/
theorem Spec.names_empty :
    parseNamesField (writeString []) = some [] := sorry

/-- An ed25519 blob with a fixed pattern key, written and
    read back. -/
theorem Spec.blob_ed25519_round :
    readBlob (writeBlob (KeyBlob.ed25519
      [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
       16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31])) =
    some (KeyBlob.ed25519
      [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
       16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]) :=
  sorry

/-- A small RSA blob (modulus 3233, exponent 17), written and
    read back. -/
theorem Spec.blob_rsa_round :
    readBlob (writeBlob (KeyBlob.rsa 17 3233)) =
      some (KeyBlob.rsa 17 3233) := sorry

/-! ## Refused inputs

Single inputs the readers refuse, one for each headline rule
of `SPEC.md`. The differential tests cover these rules on
many more inputs; these statements pin them so a reader of
the specification can check each rule against one concrete
case. -/

/-- A lone zero byte is not the encoding of zero: zero is the
    empty content. -/
theorem Spec.mpint_lone_zero_rejected :
    parseMpintField [0, 0, 0, 1, 0] = none := sorry

/-- A leading zero byte whose next byte has its high bit
    clear could be dropped, so the field is refused. -/
theorem Spec.mpint_extra_zero_rejected :
    parseMpintField [0, 0, 0, 2, 0, 127] = none := sorry

/-- A leading 255 byte whose next byte has its high bit set
    could be dropped, so the field is refused. -/
theorem Spec.mpint_extra_ff_rejected :
    parseMpintField [0, 0, 0, 2, 255, 128] = none := sorry

/-- An mpint field whose length says two content bytes but
    only one follows is refused: the reader never invents
    bytes. -/
theorem Spec.mpint_truncated_rejected :
    parseMpintField [0, 0, 0, 2, 237] = none := sorry

/-- A string field whose length says five bytes but only two
    follow is refused. -/
theorem Spec.string_length_overrun_rejected :
    parseStringField [0, 0, 0, 5, 1, 2] = none := sorry

/-- A name holding a byte outside the name rule (here the
    byte 1) is refused. -/
theorem Spec.names_bad_byte_rejected :
    parseNamesField (writeString [65, 1]) = none := sorry

/-- A name-list whose content is a single comma holds two
    empty names, and is refused. -/
theorem Spec.names_comma_rejected :
    parseNamesField (writeString [44]) = none := sorry

/-- An ed25519 key string of 31 bytes is refused: the key is
    exactly 32 bytes. -/
theorem Spec.blob_ed25519_short_key_rejected :
    readBlob (writeString algEd25519 ++
      writeString (List.replicate 31 7)) = none := sorry

/-- A blob whose key length field says 40 bytes but only 32
    follow is refused. -/
theorem Spec.blob_length_overrun_rejected :
    readBlob (writeString algEd25519 ++
      ([0, 0, 0, 40] : List UInt8) ++ List.replicate 32 7) = none :=
  sorry

/-- An algorithm name this slice does not read is refused. -/
theorem Spec.blob_unknown_alg_rejected :
    readBlob (writeString (strBytes "ssh-dss") ++
      writeString (List.replicate 32 7)) = none := sorry
