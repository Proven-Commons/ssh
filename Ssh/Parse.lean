/-
  SSH wire readers, following RFC 4251 section 5 and RFC 4253
  section 6.6.

  Each reader takes a byte list and gives back the value and the
  bytes that remain, or nothing when the bytes do not hold a
  value of its type. A length that runs past the end of the
  input is turned away, and an mpint that is not in the minimal
  form is turned away.
-/

import Ssh.Value

namespace Ssh

/-- Take exactly `n` bytes from the front of the input: those
    bytes and the rest, or nothing when fewer than `n` bytes
    remain. -/
def readBytes : Nat → List UInt8 → Option (List UInt8 × List UInt8)
  | 0, bs => some ([], bs)
  | _ + 1, [] => none
  | n + 1, b :: bs =>
    match readBytes n bs with
    | some (chunk, rest) => some (b :: chunk, rest)
    | none => none

/-- The unfolding rule for `readBytes` at width zero. -/
theorem readBytes_zero (bs : List UInt8) :
    readBytes 0 bs = some ([], bs) := by
  rw [readBytes]

/-- The unfolding rule for `readBytes` at a successor width on
    empty input. -/
theorem readBytes_succ_nil (n : Nat) :
    readBytes (n + 1) ([] : List UInt8) = none := by
  rw [readBytes]

/-- The unfolding rule for `readBytes` at a successor width on a
    list with a head byte. -/
theorem readBytes_succ_cons (n : Nat) (b : UInt8) (bs : List UInt8) :
    readBytes (n + 1) (b :: bs) =
      match readBytes n bs with
      | some (chunk, rest) => some (b :: chunk, rest)
      | none => none := by
  rw [readBytes]

/-- Read one byte. -/
def readByte : List UInt8 → Option (UInt8 × List UInt8)
  | b :: rest => some (b, rest)
  | [] => none

/-- Read a boolean: byte 0 is false, and any nonzero byte is
    true, as RFC 4251 states. -/
def readBool (bs : List UInt8) : Option (Bool × List UInt8) :=
  match readByte bs with
  | some (b, rest) => some (b ≠ 0, rest)
  | none => none

/-- Read a fixed width unsigned number: `k` bytes, big endian. -/
def readNatField (k : Nat) (bs : List UInt8) : Option (Nat × List UInt8) :=
  match readBytes k bs with
  | some (chunk, rest) => some (magOf chunk, rest)
  | none => none

/-- Read a uint32: four bytes, big endian. -/
def readUInt32 (bs : List UInt8) : Option (Nat × List UInt8) :=
  readNatField 4 bs

/-- Read a uint64: eight bytes, big endian. -/
def readUInt64 (bs : List UInt8) : Option (Nat × List UInt8) :=
  readNatField 8 bs

/-- Read a string: a uint32 length, then that many bytes. A
    length that runs past the end of the input is turned away. -/
def readString (bs : List UInt8) : Option (List UInt8 × List UInt8) :=
  (readBytes 4 bs).bind fun lenPart =>
    readBytes (magOf lenPart.1) lenPart.2

/-- Split content bytes at commas: the names between the commas,
    empty names kept, so the caller can turn them away. -/
def consName (b : UInt8) : List (List UInt8) → List (List UInt8)
  | [] => [[b]]
  | h :: t => (b :: h) :: t

/-- Split at commas, into the names the commas part. -/
def splitComma : List UInt8 → List (List UInt8)
  | [] => [[]]
  | b :: bs =>
    if b = 44 then [] :: splitComma bs
    else consName b (splitComma bs)

/-- Read the names in a name-list's content bytes: nothing when
    any name is empty or holds a byte that a name forbids. Empty
    content is the empty name-list. -/
def parseNames (bs : List UInt8) : Option (List (List UInt8)) :=
  if bs.isEmpty then some []
  else (splitComma bs).mapM (fun n => if validName n then some n else none)

/-- Read a name-list: a string whose content is names parted by
    commas. -/
def readNames (bs : List UInt8) : Option (List (List UInt8) × List UInt8) :=
  (readString bs).bind fun part =>
    (parseNames part.1).map fun names => (names, part.2)

/-- The minimal form test for mpint content bytes. A leading
    zero byte is allowed only to hold the sign of a following
    byte whose high bit is set, and a leading 255 byte only
    when the following byte's high bit is clear: any other
    leading byte could be dropped without changing the value.
    A single zero byte also fails: zero is the empty string. -/
def mpintMinimal : List UInt8 → Bool
  | [] => true
  | [b] => b ≠ 0
  | b0 :: b1 :: _ =>
    (b0 ≠ 0 || 128 ≤ b1.toNat) && (b0 ≠ 255 || b1.toNat < 128)

/-- The value of mpint content bytes: two's complement, big
    endian. The empty list is zero. -/
def mpintValue : List UInt8 → Int
  | [] => 0
  | b :: bs =>
    let all := b :: bs
    if 128 ≤ b.toNat then (magOf all : Int) - 256 ^ all.length
    else (magOf all : Int)

/-- Read an mpint: a string whose content is the value in
    minimal two's complement form. Content that is not minimal
    is turned away. -/
def readMpint (bs : List UInt8) : Option (Int × List UInt8) :=
  (readString bs).bind fun part =>
    if mpintMinimal part.1 then some (mpintValue part.1, part.2)
    else none

/-- Read a public key blob from bytes that the blob must
    consume exactly: the algorithm name as a string, then the
    fields of that algorithm, per RFC 4253 section 6.6. An
    ed25519 key string of any length other than 32 is turned
    away, and an RSA key whose `e` or `n` is not positive is
    turned away. Any other algorithm name is turned away in
    this slice. -/
def readBlob (bs : List UInt8) : Option KeyBlob :=
  (readString bs).bind fun first =>
    if first.1 = algEd25519 then
      (readString first.2).bind fun kp =>
        if kp.2.isEmpty && kp.1.length = 32 then some (KeyBlob.ed25519 kp.1)
        else none
    else if first.1 = algRsa then
      (readMpint first.2).bind fun ep =>
        (readMpint ep.2).bind fun np =>
          if np.2.isEmpty && 0 < ep.1 && 0 < np.1 then
            some (KeyBlob.rsa ep.1 np.1)
          else none
    else none

/-! ## Whole field readers, for the command line tool

  Each takes bytes that must hold exactly one field, with
  nothing left over. -/

/-- Read bytes that hold exactly one string field. -/
def parseStringField (bs : List UInt8) : Option (List UInt8) :=
  match readString bs with
  | some (v, []) => some v
  | _ => none

/-- Read bytes that hold exactly one name-list field. -/
def parseNamesField (bs : List UInt8) : Option (List (List UInt8)) :=
  match readNames bs with
  | some (v, []) => some v
  | _ => none

/-- Read bytes that hold exactly one mpint field. -/
def parseMpintField (bs : List UInt8) : Option Int :=
  match readMpint bs with
  | some (v, []) => some v
  | _ => none

end Ssh
