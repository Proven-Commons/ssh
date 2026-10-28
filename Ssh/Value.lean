/-
  SSH wire values and the writers, following RFC 4251 section 5
  and RFC 4253 section 6.6.

  Each type of RFC 4251 section 5 has a writer here: byte,
  boolean, uint32, uint64, string, name-list, and mpint. On top
  of the types sits the public key blob of RFC 4253 section 6.6,
  for the two algorithms this slice covers: `ssh-ed25519` and
  `ssh-rsa`.

  A string is held as raw bytes; whether the bytes are text is
  not this slice's question. A name-list is held as a list of
  names, each name a list of bytes. An mpint is held as a Lean
  `Int`; its writer always writes the minimal two's complement
  form the RFC requires.
-/

namespace Ssh

/-! ## Byte arithmetic shared by the writers and the readers -/

/-- The unsigned value of a byte list read big endian: the first
    byte is the most significant. -/
def magOf : List UInt8 → Nat
  | [] => 0
  | b :: bs => b.toNat * 256 ^ bs.length + magOf bs

/-- Write a natural number in exactly `k` bytes, big endian.
    Numbers too wide for the width lose their high bytes: the
    result is the number modulo 256 ^ k. -/
def writeBE : Nat → Nat → List UInt8
  | 0, _ => []
  | k + 1, n => ((n / 256 ^ k) % 256).toUInt8 :: writeBE k (n % 256 ^ k)

/-- The unfolding rule for `writeBE` at a successor width. -/
theorem writeBE_succ (k n : Nat) :
    writeBE (k + 1) n = ((n / 256 ^ k) % 256).toUInt8 :: writeBE k (n % 256 ^ k) := by
  rw [writeBE]

/-- A big endian writing is exactly as long as its width. -/
theorem writeBE_length : ∀ (k n : Nat), (writeBE k n).length = k
  | 0, _ => rfl
  | k + 1, n => by rw [writeBE_succ]; simp [writeBE_length k]

/-! ## The minimal byte form of a natural number

  The mpint writer rests on the shortest big endian byte list
  that holds a natural number: no leading zero byte, and the
  empty list for zero. The definition recurses on a fuel count
  so the kernel can compute with it; `bytesOfNat` runs it with
  the number itself as fuel, which is always enough, since each
  step divides by 256. -/

/-- The minimal big endian bytes of `n`, computed with `fuel`
    steps of division by 256. With too little fuel the result is
    cut short; the lemmas in the proofs use it only with fuel
    that covers the number. -/
def bytesOfNatGo : Nat → Nat → List UInt8
  | 0, _ => []
  | fuel + 1, n =>
    if n = 0 then []
    else bytesOfNatGo fuel (n / 256) ++ [(n % 256).toUInt8]

/-- The minimal big endian bytes of a natural number: the empty
    list for zero, and otherwise a list whose first byte is not
    zero. -/
def bytesOfNat (n : Nat) : List UInt8 := bytesOfNatGo n n

/-! ## The writers, one per type -/

/-- Write one byte. -/
def writeByte (b : UInt8) : List UInt8 := [b]

/-- Write a boolean: 1 for true, 0 for false. The reader takes
    any nonzero byte as true; the writer only ever writes 0 or
    1, so a byte like 7 reads as true and writes back as 1. -/
def writeBool (b : Bool) : List UInt8 := [if b then 1 else 0]

/-- Write a uint32: four bytes, big endian. -/
def writeUInt32 (n : Nat) : List UInt8 := writeBE 4 n

/-- Write a uint64: eight bytes, big endian. -/
def writeUInt64 (n : Nat) : List UInt8 := writeBE 8 n

/-- Write a string: a uint32 length, then that many bytes. A
    string too long for the length field (2^32 bytes or more)
    cannot be written faithfully; the round trip states its
    length bound as a hypothesis. -/
def writeString (bs : List UInt8) : List UInt8 :=
  writeBE 4 bs.length ++ bs

/-- A byte is allowed in a name when it is printable US-ASCII
    other than the comma that parts names: codes 33 to 126,
    comma (44) left out. -/
def nameByteOk (b : UInt8) : Bool :=
  (33 ≤ b.toNat && b.toNat ≤ 126) && b ≠ 44

/-- A name is good when it is nonempty and every byte is allowed
    in a name. -/
def validName (n : List UInt8) : Bool :=
  !n.isEmpty && n.all nameByteOk

/-- The content bytes of a name-list: the names joined by single
    commas. The empty list of names gives empty content. -/
def namesContent : List (List UInt8) → List UInt8
  | [] => []
  | [n] => n
  | n :: m :: rest => n ++ [44] ++ namesContent (m :: rest)

/-- Write a name-list: its content carried as a string. -/
def writeNames (names : List (List UInt8)) : List UInt8 :=
  writeString (namesContent names)

/-- The complement of a byte: 255 minus the byte. -/
def complByte (b : UInt8) : UInt8 := (255 - b.toNat).toUInt8

/-- The mpint content bytes for a nonnegative value, from the
    minimal bytes of the number: a leading zero byte exactly
    when the first byte's high bit is set, so the value does not
    read as negative. The empty byte list (zero) stays empty. -/
def mpintNatFromBytes : List UInt8 → List UInt8
  | [] => []
  | b :: bs => if 128 ≤ b.toNat then 0 :: b :: bs else b :: bs

/-- The bytes of a nonnegative mpint value, before the length
    prefix. Zero is the empty list. -/
def mpintBytesOfNat (n : Nat) : List UInt8 :=
  mpintNatFromBytes (bytesOfNat n)

/-- The mpint content bytes for a negative value, from the
    minimal bytes of the value with its sign dropped and one
    taken away. The bytes are padded on the left with one zero
    byte when they are empty or their first byte's high bit is
    set, and then every byte is complemented. -/
def mpintNegFromBytes : List UInt8 → List UInt8
  | [] => [complByte 0]
  | b :: bs =>
    if 128 ≤ b.toNat then (0 :: b :: bs).map complByte
    else (b :: bs).map complByte

/-- The bytes of a negative mpint value `-(n + 1)`, before the
    length prefix. -/
def mpintBytesOfNeg (n : Nat) : List UInt8 :=
  mpintNegFromBytes (bytesOfNat n)

/-- The content bytes of an mpint: the minimal two's complement
    form of the value. -/
def mpintBytes : Int → List UInt8
  | Int.ofNat n => mpintBytesOfNat n
  | Int.negSucc n => mpintBytesOfNeg n

/-- Write an mpint: its content bytes carried as a string. -/
def writeMpint (v : Int) : List UInt8 := writeString (mpintBytes v)

/-! ## Public key blobs (RFC 4253 section 6.6) -/

/-- The bytes of a text string, as the algorithm names in a blob
    are carried. -/
def strBytes (s : String) : List UInt8 :=
  s.toList.map (fun c => c.toNat.toUInt8)

/-- The algorithm name of an ed25519 key blob. -/
def algEd25519 : List UInt8 := strBytes "ssh-ed25519"

/-- The algorithm name of an RSA key blob. -/
def algRsa : List UInt8 := strBytes "ssh-rsa"

/-- A public key blob, for the two algorithms this slice reads:
    an ed25519 key (its 32 public key bytes), or an RSA key (the
    exponent `e` and the modulus `n`, as mpints). -/
inductive KeyBlob where
  | ed25519 : List UInt8 → KeyBlob
  | rsa : Int → Int → KeyBlob
  deriving DecidableEq, Repr

/-- Well formedness of a key blob: an ed25519 key is exactly 32
    bytes, and an RSA key's `e` and `n` are both positive, with
    mpint contents short enough for the string length field. -/
def blobWF : KeyBlob → Prop
  | KeyBlob.ed25519 key => key.length = 32
  | KeyBlob.rsa e n =>
    0 < e ∧ 0 < n ∧ (mpintBytes e).length < 2 ^ 32 ∧ (mpintBytes n).length < 2 ^ 32

/-- Write a key blob: the algorithm name as a string, then the
    fields of the algorithm. -/
def writeBlob : KeyBlob → List UInt8
  | KeyBlob.ed25519 key => writeString algEd25519 ++ writeString key
  | KeyBlob.rsa e n => writeString algRsa ++ writeMpint e ++ writeMpint n

end Ssh
