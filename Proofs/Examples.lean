/-
  Worked examples, proved by computation. The mpint examples
  are the ones printed in RFC 4251 section 5, byte for byte.
  The same examples run through the command line tool in the
  test harness, where they are checked a second time.
-/

import Ssh

namespace Ssh.Examples

open Ssh

/-! ## The mpint examples of RFC 4251 section 5 -/

theorem mpint_zero_write : writeMpint 0 = [0, 0, 0, 0] := by decide

theorem mpint_zero_read : parseMpintField [0, 0, 0, 0] = some 0 := by decide

theorem mpint_big_write :
    writeMpint 0x9a378f9b2e332a7 =
      [0, 0, 0, 8, 9, 163, 120, 249, 178, 227, 50, 167] := by decide

theorem mpint_big_read :
    parseMpintField [0, 0, 0, 8, 9, 163, 120, 249, 178, 227, 50, 167] =
      some 0x9a378f9b2e332a7 := by decide

theorem mpint_neg_small_write :
    writeMpint (-0x1234) = [0, 0, 0, 2, 237, 204] := by decide

theorem mpint_neg_small_read :
    parseMpintField [0, 0, 0, 2, 237, 204] = some (-0x1234) := by decide

theorem mpint_neg_big_write :
    writeMpint (-0xdeadbeef) = [0, 0, 0, 5, 255, 33, 82, 65, 17] := by
  decide

theorem mpint_neg_big_read :
    parseMpintField [0, 0, 0, 5, 255, 33, 82, 65, 17] =
      some (-0xdeadbeef) := by decide

/-! ## Non minimal mpint encodings are turned away -/

/-- A lone zero byte is not the encoding of zero: zero is the
    empty content. -/
theorem mpint_lone_zero_rejected :
    parseMpintField [0, 0, 0, 1, 0] = none := by decide

/-- A leading zero byte whose next byte has its high bit clear
    could be dropped, so it is turned away. -/
theorem mpint_extra_zero_rejected :
    parseMpintField [0, 0, 0, 2, 0, 127] = none := by decide

/-- A leading 255 byte whose next byte has its high bit set
    could be dropped, so it is turned away. -/
theorem mpint_extra_ff_rejected :
    parseMpintField [0, 0, 0, 2, 255, 128] = none := by decide

/-! ## Booleans: any nonzero byte reads as true, and true
    writes as the byte 1 -/

theorem bool_seven_reads_true : readBool [7] = some (true, []) := by decide

theorem bool_true_writes_one : writeBool true = [1] := by decide

/-! ## Strings and name-lists -/

theorem string_round :
    parseStringField (writeString [104, 105]) = some [104, 105] := by
  decide

theorem names_round :
    parseNamesField (writeNames [[97], [98, 99]]) = some [[97], [98, 99]] := by
  decide

theorem names_empty : parseNamesField (writeString []) = some [] := by decide

/-- A name-list whose content is a single comma holds two empty
    names, and is turned away. -/
theorem names_comma_rejected :
    parseNamesField (writeString [44]) = none := by decide

/-! ## Key blobs -/

/-- An ed25519 blob with a fixed pattern key, written and read
    back. -/
theorem blob_ed25519_round :
    readBlob (writeBlob (KeyBlob.ed25519
      [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
       16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31])) =
    some (KeyBlob.ed25519
      [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
       16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]) := by
  decide

/-- A small RSA blob (the textbook example modulus 3233, with
    exponent 17), written and read back. -/
theorem blob_rsa_round :
    readBlob (writeBlob (KeyBlob.rsa 17 3233)) =
      some (KeyBlob.rsa 17 3233) := by
  decide

/-- An ed25519 key string of 31 bytes is turned away: the key
    is exactly 32 bytes. -/
theorem blob_ed25519_short_key_rejected :
    readBlob (writeString algEd25519 ++
      writeString (List.replicate 31 7)) = none := by
  decide

/-- An algorithm name this slice does not read is turned away. -/
theorem blob_unknown_alg_rejected :
    readBlob (writeString (strBytes "ssh-dss") ++
      writeString (List.replicate 32 7)) = none := by
  decide

end Ssh.Examples
