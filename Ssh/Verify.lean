/-
  Axiom check for the claims this package makes. Run with:

    lake env lean Ssh/Verify.lean

  Every claim should list only the standard axioms (propext,
  Classical.choice, Quot.sound). A line naming the admitted gap
  axiom would mean a proof rests on a gap, and the claim is not
  proved.
-/

import Proofs
import Proofs.Examples

open Ssh.Proofs Ssh.Examples

#print axioms readByte_writeByte
#print axioms readBool_writeBool
#print axioms readUInt32_writeUInt32
#print axioms readUInt64_writeUInt64
#print axioms readString_writeString
#print axioms readNames_writeNames
#print axioms mpintValue_mpintBytes
#print axioms mpintMinimal_mpintBytes
#print axioms readMpint_writeMpint
#print axioms readBlob_writeBlob
#print axioms mpint_big_write
#print axioms blob_ed25519_round
#print axioms blob_rsa_round
