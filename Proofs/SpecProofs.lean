/-
  Proofs of the statements in `Spec.lean`, under the same names.

  The round trips are the theorems proved in
  `Proofs/RoundTrip.lean`, and the worked examples and most
  refusals are the theorems of `Proofs/Examples.lean`. The
  remaining single inputs (the RFC's 0x80 mpint example, which
  the examples file does not carry, and the length overrun and
  bad name refusals) are checked in the kernel with
  `decide +kernel`: no native evaluation, which the bar
  forbids.
-/

import Ssh
import Proofs.RoundTrip
import Proofs.Examples

open Ssh

/-! ## The round trips -/

theorem Spec.readByte_writeByte (b : UInt8) (rest : List UInt8) :
    readByte (writeByte b ++ rest) = some (b, rest) :=
  Ssh.Proofs.readByte_writeByte b rest

theorem Spec.readBool_writeBool (b : Bool) (rest : List UInt8) :
    readBool (writeBool b ++ rest) = some (b, rest) :=
  Ssh.Proofs.readBool_writeBool b rest

theorem Spec.readUInt32_writeUInt32 (n : Nat) (rest : List UInt8)
    (h : n < 2 ^ 32) :
    readUInt32 (writeUInt32 n ++ rest) = some (n, rest) :=
  Ssh.Proofs.readUInt32_writeUInt32 n rest h

theorem Spec.readUInt64_writeUInt64 (n : Nat) (rest : List UInt8)
    (h : n < 2 ^ 64) :
    readUInt64 (writeUInt64 n ++ rest) = some (n, rest) :=
  Ssh.Proofs.readUInt64_writeUInt64 n rest h

theorem Spec.readString_writeString (bs rest : List UInt8)
    (h : bs.length < 2 ^ 32) :
    readString (writeString bs ++ rest) = some (bs, rest) :=
  Ssh.Proofs.readString_writeString bs rest h

theorem Spec.readNames_writeNames (names : List (List UInt8))
    (rest : List UInt8)
    (hvalid : ∀ n ∈ names, validName n = true)
    (hlen : (namesContent names).length < 2 ^ 32) :
    readNames (writeNames names ++ rest) = some (names, rest) :=
  Ssh.Proofs.readNames_writeNames names rest hvalid hlen

theorem Spec.mpintValue_mpintBytes (v : Int) :
    mpintValue (mpintBytes v) = v :=
  Ssh.Proofs.mpintValue_mpintBytes v

theorem Spec.mpintMinimal_mpintBytes (v : Int) :
    mpintMinimal (mpintBytes v) = true :=
  Ssh.Proofs.mpintMinimal_mpintBytes v

theorem Spec.readMpint_writeMpint (v : Int) (rest : List UInt8)
    (h : (mpintBytes v).length < 2 ^ 32) :
    readMpint (writeMpint v ++ rest) = some (v, rest) :=
  Ssh.Proofs.readMpint_writeMpint v rest h

theorem Spec.readBlob_writeBlob (b : KeyBlob) (hb : blobWF b) :
    readBlob (writeBlob b) = some b :=
  Ssh.Proofs.readBlob_writeBlob b hb

/-! ## The mpint examples of RFC 4251 section 5 -/

theorem Spec.mpint_zero_write :
    writeMpint 0 = [0, 0, 0, 0] :=
  Ssh.Examples.mpint_zero_write

theorem Spec.mpint_zero_read :
    parseMpintField [0, 0, 0, 0] = some 0 :=
  Ssh.Examples.mpint_zero_read

theorem Spec.mpint_big_write :
    writeMpint 0x9a378f9b2e332a7 =
      [0, 0, 0, 8, 9, 163, 120, 249, 178, 227, 50, 167] :=
  Ssh.Examples.mpint_big_write

theorem Spec.mpint_big_read :
    parseMpintField [0, 0, 0, 8, 9, 163, 120, 249, 178, 227, 50, 167] =
      some 0x9a378f9b2e332a7 :=
  Ssh.Examples.mpint_big_read

theorem Spec.mpint_80_write :
    writeMpint 0x80 = [0, 0, 0, 2, 0, 128] := by
  decide +kernel

theorem Spec.mpint_80_read :
    parseMpintField [0, 0, 0, 2, 0, 128] = some 0x80 := by
  decide +kernel

theorem Spec.mpint_neg_small_write :
    writeMpint (-0x1234) = [0, 0, 0, 2, 237, 204] :=
  Ssh.Examples.mpint_neg_small_write

theorem Spec.mpint_neg_small_read :
    parseMpintField [0, 0, 0, 2, 237, 204] = some (-0x1234) :=
  Ssh.Examples.mpint_neg_small_read

theorem Spec.mpint_neg_big_write :
    writeMpint (-0xdeadbeef) = [0, 0, 0, 5, 255, 33, 82, 65, 17] :=
  Ssh.Examples.mpint_neg_big_write

theorem Spec.mpint_neg_big_read :
    parseMpintField [0, 0, 0, 5, 255, 33, 82, 65, 17] =
      some (-0xdeadbeef) :=
  Ssh.Examples.mpint_neg_big_read

/-! ## Worked examples -/

theorem Spec.bool_seven_reads_true :
    readBool [7] = some (true, []) :=
  Ssh.Examples.bool_seven_reads_true

theorem Spec.bool_true_writes_one :
    writeBool true = [1] :=
  Ssh.Examples.bool_true_writes_one

theorem Spec.string_round :
    parseStringField (writeString [104, 105]) = some [104, 105] :=
  Ssh.Examples.string_round

theorem Spec.names_round :
    parseNamesField (writeNames [[97], [98, 99]]) =
      some [[97], [98, 99]] :=
  Ssh.Examples.names_round

theorem Spec.names_empty :
    parseNamesField (writeString []) = some [] :=
  Ssh.Examples.names_empty

theorem Spec.blob_ed25519_round :
    readBlob (writeBlob (KeyBlob.ed25519
      [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
       16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31])) =
    some (KeyBlob.ed25519
      [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
       16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]) :=
  Ssh.Examples.blob_ed25519_round

theorem Spec.blob_rsa_round :
    readBlob (writeBlob (KeyBlob.rsa 17 3233)) =
      some (KeyBlob.rsa 17 3233) :=
  Ssh.Examples.blob_rsa_round

/-! ## Refused inputs -/

theorem Spec.mpint_lone_zero_rejected :
    parseMpintField [0, 0, 0, 1, 0] = none :=
  Ssh.Examples.mpint_lone_zero_rejected

theorem Spec.mpint_extra_zero_rejected :
    parseMpintField [0, 0, 0, 2, 0, 127] = none :=
  Ssh.Examples.mpint_extra_zero_rejected

theorem Spec.mpint_extra_ff_rejected :
    parseMpintField [0, 0, 0, 2, 255, 128] = none :=
  Ssh.Examples.mpint_extra_ff_rejected

theorem Spec.mpint_truncated_rejected :
    parseMpintField [0, 0, 0, 2, 237] = none := by
  decide +kernel

theorem Spec.string_length_overrun_rejected :
    parseStringField [0, 0, 0, 5, 1, 2] = none := by
  decide +kernel

theorem Spec.names_bad_byte_rejected :
    parseNamesField (writeString [65, 1]) = none := by
  decide +kernel

theorem Spec.names_comma_rejected :
    parseNamesField (writeString [44]) = none :=
  Ssh.Examples.names_comma_rejected

theorem Spec.blob_ed25519_short_key_rejected :
    readBlob (writeString algEd25519 ++
      writeString (List.replicate 31 7)) = none :=
  Ssh.Examples.blob_ed25519_short_key_rejected

theorem Spec.blob_length_overrun_rejected :
    readBlob (writeString algEd25519 ++
      ([0, 0, 0, 40] : List UInt8) ++ List.replicate 32 7) = none := by
  decide +kernel

theorem Spec.blob_unknown_alg_rejected :
    readBlob (writeString (strBytes "ssh-dss") ++
      writeString (List.replicate 32 7)) = none :=
  Ssh.Examples.blob_unknown_alg_rejected
