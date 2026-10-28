/-
  Round trip proofs for the SSH wire types: reading a written
  value gives the value back.
-/

import Ssh

namespace Ssh.Proofs

open Ssh

/-! ## Byte arithmetic -/

theorem magOf_cons (b : UInt8) (bs : List UInt8) :
    magOf (b :: bs) = b.toNat * 256 ^ bs.length + magOf bs := rfl

theorem magOf_append : ∀ (a b : List UInt8),
    magOf (a ++ b) = magOf a * 256 ^ b.length + magOf b
  | [], b => by simp [magOf]
  | a :: as, b => by
    rw [List.cons_append, magOf_cons, magOf_append as b, magOf_cons,
      List.length_append, Nat.pow_add, Nat.add_mul, Nat.mul_assoc,
      Nat.add_assoc]

theorem magOf_lt : ∀ (bs : List UInt8), magOf bs < 256 ^ bs.length
  | [] => by simp [magOf]
  | b :: bs => by
    have ih := magOf_lt bs
    have hb : b.toNat < 256 := UInt8.toNat_lt_size b
    rw [magOf_cons, List.length_cons, Nat.pow_succ]
    calc b.toNat * 256 ^ bs.length + magOf bs
        ≤ 255 * 256 ^ bs.length + magOf bs :=
          Nat.add_le_add_right (Nat.mul_le_mul_right _ (by omega)) _
      _ < 255 * 256 ^ bs.length + 256 ^ bs.length :=
          Nat.add_lt_add_left ih _
      _ = 256 ^ bs.length * 256 := by omega

theorem magOf_writeBE : ∀ (k n : Nat), n < 256 ^ k → magOf (writeBE k n) = n
  | 0, n, hn => by
    rw [Nat.pow_zero] at hn
    have hn0 : n = 0 := by omega
    rw [hn0]
    rfl
  | k + 1, n, hn => by
    have hP : 0 < 256 ^ k := Nat.pow_pos (by decide)
    have hlt : n / 256 ^ k < 256 := by
      rw [Nat.pow_succ] at hn
      exact Nat.div_lt_of_lt_mul hn
    have hd : ((n / 256 ^ k) % 256).toUInt8.toNat = n / 256 ^ k := by
      have h1 : ((n / 256 ^ k) % 256).toUInt8.toNat = (n / 256 ^ k) % 256 :=
        UInt8.toNat_ofNat_of_lt (Nat.mod_lt _ (by decide : 0 < 256))
      rw [h1, Nat.mod_eq_of_lt hlt]
    rw [writeBE_succ, magOf_cons, writeBE_length, hd,
      magOf_writeBE k (n % 256 ^ k) (Nat.mod_lt _ hP),
      Nat.mul_comm (n / 256 ^ k) (256 ^ k)]
    exact Nat.div_add_mod n (256 ^ k)

theorem magOf_replicate_zero : ∀ (m : Nat) (bs : List UInt8),
    magOf (List.replicate m 0 ++ bs) = magOf bs
  | 0, bs => by simp
  | m + 1, bs => by
    rw [List.replicate_succ, List.cons_append, magOf_cons,
      magOf_replicate_zero m bs]
    simp

/-! ## Taking bytes from the front -/

theorem readBytes_append : ∀ (n : Nat) (chunk rest : List UInt8),
    chunk.length = n → readBytes n (chunk ++ rest) = some (chunk, rest)
  | 0, [], _, _ => rfl
  | 0, _ :: _, _, h => by simp at h
  | _ + 1, [], _, h => by simp at h
  | n + 1, b :: chunk, rest, h => by
    have h' : chunk.length = n := by
      rw [List.length_cons] at h
      omega
    rw [List.cons_append, readBytes_succ_cons,
      readBytes_append n chunk rest h']

theorem readBytes_some : ∀ {n : Nat} {bs chunk rest : List UInt8},
    readBytes n bs = some (chunk, rest) →
    chunk.length = n ∧ chunk ++ rest = bs := by
  intro n
  induction n with
  | zero =>
    intro bs chunk rest h
    rw [readBytes_zero] at h
    cases h
    exact ⟨rfl, rfl⟩
  | succ n ih =>
    intro bs chunk rest h
    cases bs with
    | nil => rw [readBytes_succ_nil] at h; cases h
    | cons b bs =>
      rw [readBytes_succ_cons] at h
      cases h' : readBytes n bs with
      | none => rw [h'] at h; cases h
      | some p =>
        obtain ⟨c, r⟩ := p
        rw [h'] at h
        cases h
        have ih' := ih h'
        refine ⟨?_, ?_⟩
        · rw [List.length_cons, ih'.1]
        · rw [List.cons_append, ih'.2]

theorem readBytes_none_of_short : ∀ {n : Nat} {bs : List UInt8},
    bs.length < n → readBytes n bs = none := by
  intro n
  induction n with
  | zero => intro bs h; simp at h
  | succ n ih =>
    intro bs h
    cases bs with
    | nil => exact readBytes_succ_nil n
    | cons b bs =>
      rw [readBytes_succ_cons]
      have h' : bs.length < n := by
        rw [List.length_cons] at h
        omega
      rw [ih h']

/-! ## The small types -/

theorem readByte_writeByte (b : UInt8) (rest : List UInt8) :
    readByte (writeByte b ++ rest) = some (b, rest) := rfl

theorem readBool_writeBool (b : Bool) (rest : List UInt8) :
    readBool (writeBool b ++ rest) = some (b, rest) := by
  cases b <;> rfl

theorem readNatField_writeBE (k n : Nat) (rest : List UInt8)
    (h : n < 256 ^ k) :
    readNatField k (writeBE k n ++ rest) = some (n, rest) := by
  unfold readNatField
  rw [readBytes_append k (writeBE k n) rest (writeBE_length k n)]
  show some (magOf (writeBE k n), rest) = some (n, rest)
  rw [magOf_writeBE k n h]

theorem readUInt32_writeUInt32 (n : Nat) (rest : List UInt8)
    (h : n < 2 ^ 32) :
    readUInt32 (writeUInt32 n ++ rest) = some (n, rest) := by
  apply readNatField_writeBE
  have e : (256 : Nat) ^ 4 = 2 ^ 32 := by decide
  rwa [e]

theorem readUInt64_writeUInt64 (n : Nat) (rest : List UInt8)
    (h : n < 2 ^ 64) :
    readUInt64 (writeUInt64 n ++ rest) = some (n, rest) := by
  apply readNatField_writeBE
  have e : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
  rwa [e]


/-! ## Strings -/

/-- Binding a `some` applies the function at once. -/
theorem bind_some_apply {α β : Type} (f : α → Option β) (a : α) :
    (some a).bind f = f a := rfl

theorem readString_writeString (bs rest : List UInt8)
    (h : bs.length < 2 ^ 32) :
    readString (writeString bs ++ rest) = some (bs, rest) := by
  have h256 : bs.length < 256 ^ 4 := by
    have e : (256 : Nat) ^ 4 = 2 ^ 32 := by decide
    rwa [e]
  unfold readString writeString
  rw [List.append_assoc,
    readBytes_append 4 (writeBE 4 bs.length) (bs ++ rest) (writeBE_length 4 _),
    bind_some_apply]
  dsimp only
  rw [magOf_writeBE 4 bs.length h256,
    readBytes_append bs.length bs rest rfl]

/-! ## Name-lists -/

/-- Prepending a non-comma byte to the first name of a split. -/
theorem consName_cons (b : UInt8) (h : List UInt8) (t : List (List UInt8)) :
    consName b (h :: t) = (b :: h) :: t := rfl

theorem consName_ne_nil (b : UInt8) (l : List (List UInt8)) :
    consName b l ≠ [] := by
  cases l <;> simp [consName]

theorem splitComma_ne_nil : ∀ (bs : List UInt8), splitComma bs ≠ []
  | [] => by simp [splitComma]
  | b :: bs => by
    by_cases hb : b = 44
    · simp [splitComma, hb]
    · simp [splitComma, hb, consName_ne_nil]

theorem splitComma_comma (bs : List UInt8) :
    splitComma (44 :: bs) = [] :: splitComma bs := by
  simp [splitComma]

theorem splitComma_cons_ne {b : UInt8} (hb : b ≠ 44) (bs : List UInt8) :
    splitComma (b :: bs) = consName b (splitComma bs) := by
  simp [splitComma, hb]

/-- Splitting a name that holds no comma, set in front of other
    bytes: the name lands whole on the first part of the split. -/
theorem splitComma_append_noComma : ∀ (name rest : List UInt8)
    (c : List UInt8) (cs : List (List UInt8)),
    splitComma rest = c :: cs → (∀ b ∈ name, b ≠ 44) →
    splitComma (name ++ rest) = (name ++ c) :: cs
  | [], rest, c, cs, h, _ => by simpa using h
  | b :: name, rest, c, cs, h, hb => by
    have hb0 : b ≠ 44 := hb b (by simp)
    have hb' : ∀ x ∈ name, x ≠ 44 := fun x hx => hb x (List.mem_cons_of_mem b hx)
    rw [List.cons_append, splitComma_cons_ne hb0,
      splitComma_append_noComma name rest c cs h hb']
    simp only [consName_cons, List.cons_append]

theorem namesContent_single (n : List UInt8) :
    namesContent [n] = n := rfl

theorem namesContent_cons_cons (n m : List UInt8) (rest : List (List UInt8)) :
    namesContent (n :: m :: rest) = n ++ [44] ++ namesContent (m :: rest) := rfl

/-- Splitting the content of a name-list gives the names back,
    when no name holds a comma. -/
theorem splitComma_namesContent : ∀ (names : List (List UInt8)),
    names ≠ [] → (∀ n ∈ names, ∀ b ∈ n, b ≠ 44) →
    splitComma (namesContent names) = names := by
  intro names
  induction names with
  | nil => intro h; cases h rfl
  | cons n names ih =>
    intro _ hcomma
    cases names with
    | nil =>
      rw [namesContent_single, ← List.append_nil n]
      exact splitComma_append_noComma n [] [] []
        (by simp [splitComma]) (fun b hb => hcomma n (by simp) b hb)
    | cons m rest =>
      have hsplit : splitComma ([44] ++ namesContent (m :: rest)) = [] :: (m :: rest) := by
        rw [show [44] ++ namesContent (m :: rest) = 44 :: namesContent (m :: rest) from rfl,
          splitComma_comma]
        exact congrArg (fun x => [] :: x)
          (ih (by simp) (fun x hx => hcomma x (List.mem_cons_of_mem n hx)))
      rw [namesContent_cons_cons, List.append_assoc,
        splitComma_append_noComma n ([44] ++ namesContent (m :: rest)) []
          (m :: rest) hsplit (fun b hb => hcomma n (by simp) b hb),
        List.append_nil]

/-- A good name holds no comma: the comma is the one printable
    byte its byte rule leaves out. -/
theorem validName_noComma {n : List UInt8} (h : validName n = true) :
    ∀ b ∈ n, b ≠ 44 := by
  intro b hb
  unfold validName at h
  rw [Bool.and_eq_true] at h
  have hall : n.all nameByteOk = true := h.2
  have hb2 : nameByteOk b = true := by
    have := List.all_eq_true.mp hall b hb
    exact this
  unfold nameByteOk at hb2
  rw [Bool.and_eq_true] at hb2
  have hdec : decide (b ≠ 44) = true := hb2.2
  exact of_decide_eq_true hdec

/-- Checking a list of good names, one by one, gives the list. -/
theorem mapM_checkName : ∀ (names : List (List UInt8)),
    (∀ n ∈ names, validName n = true) →
    names.mapM (fun n => if validName n then some n else none) = some names
  | [], _ => rfl
  | n :: names, h => by
    have hn : validName n = true := h n (by simp)
    have hrest : ∀ x ∈ names, validName x = true :=
      fun x hx => h x (List.mem_cons_of_mem n hx)
    simp [hn, mapM_checkName names hrest]

/-- Reading back the content of a name-list gives the names. -/
theorem parseNames_namesContent (names : List (List UInt8))
    (h : ∀ n ∈ names, validName n = true) :
    parseNames (namesContent names) = some names := by
  cases names with
  | nil => rfl
  | cons n names =>
    have hn : validName n = true := h n (by simp)
    have hnne : n ≠ [] := by
      intro hne
      rw [hne] at hn
      simp [validName] at hn
    have hcontent : (namesContent (n :: names)).isEmpty = false := by
      cases names with
      | nil =>
        rw [namesContent_single]
        cases n with
        | nil => exact absurd rfl hnne
        | cons b bs => rfl
      | cons m rest =>
        rw [namesContent_cons_cons]
        cases n with
        | nil => exact absurd rfl hnne
        | cons b bs => rfl
    unfold parseNames
    rw [hcontent]
    simp only [Bool.false_eq_true, ite_false]
    rw [splitComma_namesContent (n :: names) (by simp)
      (fun x hx b hb => validName_noComma (h x hx) b hb)]
    exact mapM_checkName _ h

/-- Reading a written name-list gives the name-list back. -/
theorem readNames_writeNames (names : List (List UInt8)) (rest : List UInt8)
    (hvalid : ∀ n ∈ names, validName n = true)
    (hlen : (namesContent names).length < 2 ^ 32) :
    readNames (writeNames names ++ rest) = some (names, rest) := by
  unfold readNames writeNames
  rw [readString_writeString _ _ hlen, bind_some_apply]
  dsimp only
  rw [parseNames_namesContent names hvalid]
  rfl

/-! ## The minimal bytes of a natural number -/

theorem bytesOfNatGo_succ (f n : Nat) :
    bytesOfNatGo (f + 1) n =
      if n = 0 then []
      else bytesOfNatGo f (n / 256) ++ [(n % 256).toUInt8] := by
  rw [bytesOfNatGo]

theorem bytesOfNatGo_zero : ∀ (f : Nat), bytesOfNatGo f 0 = []
  | 0 => rfl
  | f + 1 => by rw [bytesOfNatGo_succ]; exact if_pos rfl

theorem lt_256_pow_self (n : Nat) : n < 256 ^ n := by
  have h1 : n + 1 ≤ 2 ^ n := Nat.lt_two_pow_self
  have h2 : 2 ^ n ≤ 256 ^ n := Nat.pow_le_pow_left (by decide) n
  omega

theorem bytesOfNatGo_magOf : ∀ (f n : Nat),
    n < 256 ^ f → magOf (bytesOfNatGo f n) = n := by
  intro f
  induction f with
  | zero =>
    intro n hn
    rw [Nat.pow_zero] at hn
    have hn0 : n = 0 := by omega
    rw [hn0]
    rfl
  | succ f ih =>
    intro n hn
    rw [bytesOfNatGo_succ]
    by_cases hn0 : n = 0
    · rw [if_pos hn0, hn0]
      rfl
    · rw [if_neg hn0]
      have hlt : n / 256 < 256 ^ f := by
        rw [Nat.pow_succ, Nat.mul_comm (256 ^ f) 256] at hn
        exact Nat.div_lt_of_lt_mul hn
      have hsingle : magOf [(n % 256).toUInt8] = n % 256 := by
        simp [magOf]
      rw [magOf_append, ih _ hlt, hsingle, List.length_singleton, Nat.pow_one,
        Nat.mul_comm (n / 256) 256]
      exact Nat.div_add_mod n 256

theorem bytesOfNatGo_head : ∀ (f n : Nat), 0 < n → n < 256 ^ f →
    ∃ b bs, bytesOfNatGo f n = b :: bs ∧ b ≠ 0 := by
  intro f
  induction f with
  | zero =>
    intro n _ hn
    rw [Nat.pow_zero] at hn
    omega
  | succ f ih =>
    intro n hn0 hn
    rw [bytesOfNatGo_succ, if_neg (by omega : n ≠ 0)]
    by_cases hd : n / 256 = 0
    · rw [hd, bytesOfNatGo_zero]
      have hn256 : n < 256 := by
        rcases Nat.lt_or_ge n 256 with h | h
        · exact h
        · have hpos := Nat.div_pos h (by decide : 0 < 256)
          omega
      have hmod : n % 256 = n := Nat.mod_eq_of_lt hn256
      refine ⟨(n % 256).toUInt8, [], by simp, ?_⟩
      have h1 : ((n % 256).toUInt8).toNat = n := by
        have h2 : ((n % 256).toUInt8).toNat = n % 256 :=
          UInt8.toNat_ofNat_of_lt (Nat.mod_lt _ (by decide : 0 < 256))
        rw [h2, hmod]
      intro hcon
      have h2 : ((n % 256).toUInt8).toNat = 0 := by
        rw [hcon]
        decide
      omega
    · have hd0 : 0 < n / 256 := by omega
      have hlt : n / 256 < 256 ^ f := by
        rw [Nat.pow_succ, Nat.mul_comm (256 ^ f) 256] at hn
        exact Nat.div_lt_of_lt_mul hn
      obtain ⟨b, bs, hgo, hb0⟩ := ih _ hd0 hlt
      exact ⟨b, bs ++ [(n % 256).toUInt8], by rw [hgo, List.cons_append], hb0⟩

theorem magOf_bytesOfNat (n : Nat) : magOf (bytesOfNat n) = n :=
  bytesOfNatGo_magOf n n (lt_256_pow_self n)

theorem bytesOfNat_head {n : Nat} (h : 0 < n) :
    ∃ b bs, bytesOfNat n = b :: bs ∧ b ≠ 0 :=
  bytesOfNatGo_head n n h (lt_256_pow_self n)

theorem bytesOfNat_eq_nil {n : Nat} : bytesOfNat n = [] ↔ n = 0 := by
  constructor
  · intro h
    rcases Nat.lt_or_ge n 1 with h1 | h1
    · omega
    · obtain ⟨b, bs, h', _⟩ := bytesOfNat_head (by omega : 0 < n)
      rw [h] at h'
      cases h'
  · intro h
    rw [h]
    rfl

theorem bytesOfNat_head_ne {n : Nat} {b : UInt8} {bs : List UInt8}
    (h : bytesOfNat n = b :: bs) : b ≠ 0 := by
  cases hn : n with
  | zero =>
    rw [hn] at h
    simp [bytesOfNat, bytesOfNatGo] at h
  | succ k =>
    rw [hn] at h
    obtain ⟨b', bs', h', hb'⟩ := bytesOfNat_head (Nat.succ_pos k)
    rw [h] at h'
    cases h'
    exact hb'

/-! ## Complemented bytes -/

theorem complByte_toNat (b : UInt8) : (complByte b).toNat = 255 - b.toNat := by
  unfold complByte
  have hb : b.toNat < 256 := UInt8.toNat_lt_size b
  exact UInt8.toNat_ofNat_of_lt (show 255 - b.toNat < 256 by omega)

theorem subComplArith (P X M : Nat) (hM : M < P) (hX : X ≤ 255 * P) :
    255 * P - X + (P - 1 - M) = P * 256 - 1 - (X + M) := by omega

theorem magOf_map_compl : ∀ (bs : List UInt8),
    magOf (bs.map complByte) = 256 ^ bs.length - 1 - magOf bs
  | [] => by simp [magOf]
  | b :: bs => by
    have ih := magOf_map_compl bs
    have hbound := magOf_lt bs
    have hb : b.toNat < 256 := UInt8.toNat_lt_size b
    rw [List.map_cons, magOf_cons, List.length_map, ih, complByte_toNat,
      List.length_cons, Nat.pow_succ, magOf_cons, Nat.sub_mul]
    exact subComplArith _ _ _ hbound
      (Nat.mul_le_mul (by omega : b.toNat ≤ 255) (Nat.le_refl _))

theorem cast_pow_256 (L : Nat) : ((256 ^ L : Nat) : Int) = (256 : Int) ^ L := by
  induction L with
  | zero => rfl
  | succ k ih =>
    rw [Nat.pow_succ]
    show ((256 ^ k : Nat) : Int) * ((256 : Nat) : Int) = (256 : Int) ^ k * 256
    rw [ih]
    rfl

/-! ## The mpint core -/

theorem mpintNatFromBytes_cons (b : UInt8) (bs : List UInt8) :
    mpintNatFromBytes (b :: bs) =
      if 128 ≤ b.toNat then 0 :: b :: bs else b :: bs := rfl

theorem mpintNegFromBytes_nil : mpintNegFromBytes [] = [complByte 0] := rfl

theorem mpintNegFromBytes_cons (b : UInt8) (bs : List UInt8) :
    mpintNegFromBytes (b :: bs) =
      if 128 ≤ b.toNat then (0 :: b :: bs).map complByte
      else (b :: bs).map complByte := rfl

theorem mpintValue_cons (b : UInt8) (bs : List UInt8) :
    mpintValue (b :: bs) =
      if 128 ≤ b.toNat then (magOf (b :: bs) : Int) - 256 ^ (b :: bs).length
      else (magOf (b :: bs) : Int) := rfl

theorem mpintMinimal_single (b : UInt8) :
    mpintMinimal [b] = decide (b ≠ 0) := rfl

theorem mpintMinimal_cons_cons (b0 b1 : UInt8) (bs : List UInt8) :
    mpintMinimal (b0 :: b1 :: bs) =
      ((b0 ≠ 0 || 128 ≤ b1.toNat) && (b0 ≠ 255 || b1.toNat < 128)) := rfl

theorem mpintValue_mpintBytes (v : Int) : mpintValue (mpintBytes v) = v := by
  cases v with
  | ofNat n =>
    cases n with
    | zero => rfl
    | succ m =>
      obtain ⟨b, bs, hbs, hb0⟩ := bytesOfNat_head (Nat.succ_pos m)
      have hmag : magOf (b :: bs) = m + 1 := by
        have h := magOf_bytesOfNat (m + 1)
        rw [hbs] at h
        exact h
      show mpintValue (mpintNatFromBytes (bytesOfNat (m + 1))) = ((m + 1 : Nat) : Int)
      rw [hbs, mpintNatFromBytes_cons]
      by_cases hc : 128 ≤ b.toNat
      · rw [if_pos hc, mpintValue_cons,
          if_neg (by decide : ¬ 128 ≤ (0 : UInt8).toNat), magOf_cons,
          show (0 : UInt8).toNat = 0 from rfl, Nat.zero_mul, Nat.zero_add, hmag]
      · rw [if_neg hc, mpintValue_cons, if_neg hc, hmag]
  | negSucc n =>
    cases h : bytesOfNat n with
    | nil =>
      have hn0 : n = 0 := bytesOfNat_eq_nil.1 h
      subst hn0
      rfl
    | cons b bs =>
      have hmag : magOf (b :: bs) = n := by
        have hh := magOf_bytesOfNat n
        rw [h] at hh
        exact hh
      show mpintValue (mpintNegFromBytes (bytesOfNat n)) = Int.negSucc n
      rw [h, mpintNegFromBytes_cons]
      by_cases hc : 128 ≤ b.toNat
      · rw [if_pos hc, List.map_cons, mpintValue_cons,
          if_pos (by rw [complByte_toNat]; decide : 128 ≤ (complByte 0).toNat)]
        have hmagc : magOf (complByte 0 :: (b :: bs).map complByte) =
            256 ^ ((b :: bs).length + 1) - 1 - n := by
          have h1 := magOf_map_compl (0 :: b :: bs)
          rw [List.map_cons, List.length_cons, magOf_cons, magOf_cons,
            show (0 : UInt8).toNat = 0 from rfl, Nat.zero_mul, Nat.zero_add,
            hmag] at h1
          exact h1
        have hle : n + 1 ≤ 256 ^ ((b :: bs).length + 1) := by
          have h1 : n < 256 ^ (b :: bs).length := by
            rw [← hmag]; exact magOf_lt _
          have h2 : 256 ^ (b :: bs).length ≤ 256 ^ ((b :: bs).length + 1) :=
            Nat.pow_le_pow_right (by decide) (Nat.le_succ _)
          omega
        have hcast : ((256 ^ ((b :: bs).length + 1) - 1 - n : Nat) : Int) =
            (256 : Int) ^ ((b :: bs).length + 1) - 1 - (n : Int) := by
          rw [Int.ofNat_sub (show n ≤ 256 ^ ((b :: bs).length + 1) - 1 by omega),
            Int.ofNat_sub (show 1 ≤ 256 ^ ((b :: bs).length + 1) by omega),
            Int.ofNat_one, cast_pow_256]
        rw [List.length_cons, List.length_map, hmagc, hcast]
        omega
      · rw [if_neg hc]
        cases bs with
        | nil =>
          have hn : n = b.toNat := by
            rw [← hmag]; simp [magOf]
          subst hn
          rw [List.map_cons, List.map_nil, mpintValue_cons,
            if_pos (by rw [complByte_toNat]; omega : 128 ≤ (complByte b).toNat)]
          have hm : magOf [complByte b] = 255 - b.toNat := by
            simp [magOf, complByte_toNat]
          rw [hm, show [complByte b].length = 1 from rfl,
            show (256 : Int) ^ 1 = 256 from rfl,
            Int.ofNat_sub (show b.toNat ≤ 255 by omega)]
          omega
        | cons b' bs' =>
          rw [List.map_cons, mpintValue_cons,
            if_pos (by rw [complByte_toNat]; omega : 128 ≤ (complByte b).toNat)]
          have hmagc : magOf (complByte b :: (b' :: bs').map complByte) =
              256 ^ (b :: b' :: bs').length - 1 - n := by
            have h1 := magOf_map_compl (b :: b' :: bs')
            rw [List.map_cons, hmag] at h1
            exact h1
          have hcast : ((256 ^ (b :: b' :: bs').length - 1 - n : Nat) : Int) =
              (256 : Int) ^ (b :: b' :: bs').length - 1 - (n : Int) := by
            rw [Int.ofNat_sub (show n ≤ 256 ^ (b :: b' :: bs').length - 1 by
                  have h1 : n < 256 ^ (b :: b' :: bs').length := by
                    rw [← hmag]; exact magOf_lt _
                  omega),
              Int.ofNat_sub (show 1 ≤ 256 ^ (b :: b' :: bs').length from
                Nat.one_le_pow _ _ (by decide)),
              Int.ofNat_one, cast_pow_256]
          rw [List.length_cons, List.length_map, hmagc, hcast, List.length_cons]
          omega

theorem mpintMinimal_mpintBytes (v : Int) : mpintMinimal (mpintBytes v) = true := by
  cases v with
  | ofNat n =>
    cases n with
    | zero => rfl
    | succ m =>
      obtain ⟨b, bs, hbs, hb0⟩ := bytesOfNat_head (Nat.succ_pos m)
      show mpintMinimal (mpintNatFromBytes (bytesOfNat (m + 1))) = true
      rw [hbs, mpintNatFromBytes_cons]
      by_cases hc : 128 ≤ b.toNat
      · rw [if_pos hc, mpintMinimal_cons_cons]
        simp [hc]
      · rw [if_neg hc]
        cases bs with
        | nil =>
          rw [mpintMinimal_single]
          simp [hb0]
        | cons b' bs' =>
          have hb255 : b ≠ 255 := by
            intro hh
            rw [hh] at hc
            exact hc (by decide : 128 ≤ (255 : UInt8).toNat)
          rw [mpintMinimal_cons_cons]
          simp [hb0, hb255]
  | negSucc n =>
    cases h : bytesOfNat n with
    | nil =>
      have hn0 : n = 0 := bytesOfNat_eq_nil.1 h
      subst hn0
      rfl
    | cons b bs =>
      have hb0 : b ≠ 0 := bytesOfNat_head_ne h
      have hbpos : 1 ≤ b.toNat := by
        have h2 : b.toNat ≠ 0 := by
          intro hh
          apply hb0
          exact UInt8.toNat_inj.1 (by rw [hh]; rfl)
        omega
      show mpintMinimal (mpintNegFromBytes (bytesOfNat n)) = true
      rw [h, mpintNegFromBytes_cons]
      by_cases hc : 128 ≤ b.toNat
      · rw [if_pos hc]
        have e1 : complByte 0 ≠ 0 := by decide
        have e2 : (complByte b).toNat < 128 := by
          rw [complByte_toNat]; omega
        cases bs with
        | nil =>
          rw [List.map_cons, List.map_cons, List.map_nil, mpintMinimal_cons_cons]
          simp [e1, e2]
        | cons b' bs' =>
          rw [List.map_cons, List.map_cons, mpintMinimal_cons_cons]
          simp [e1, e2]
      · rw [if_neg hc]
        have e1 : complByte b ≠ 0 := by
          intro hh
          have h2 := congrArg UInt8.toNat hh
          rw [complByte_toNat, show (0 : UInt8).toNat = 0 from rfl] at h2
          omega
        have e2 : complByte b ≠ 255 := by
          intro hh
          have h2 := congrArg UInt8.toNat hh
          rw [complByte_toNat, show (255 : UInt8).toNat = 255 from rfl] at h2
          omega
        cases bs with
        | nil =>
          rw [List.map_cons, List.map_nil, mpintMinimal_single]
          simp [e1]
        | cons b' bs' =>
          rw [List.map_cons, List.map_cons, mpintMinimal_cons_cons]
          simp [e1, e2]

theorem readMpint_writeMpint (v : Int) (rest : List UInt8)
    (h : (mpintBytes v).length < 2 ^ 32) :
    readMpint (writeMpint v ++ rest) = some (v, rest) := by
  unfold readMpint writeMpint
  rw [readString_writeString _ _ h, bind_some_apply]
  dsimp only
  rw [mpintValue_mpintBytes, mpintMinimal_mpintBytes, if_pos rfl]

theorem readBlob_writeBlob (b : KeyBlob) (hb : blobWF b) :
    readBlob (writeBlob b) = some b := by
  cases b with
  | ed25519 key =>
    have hk : key.length = 32 := hb
    show readBlob (writeString algEd25519 ++ writeString key) =
      some (KeyBlob.ed25519 key)
    unfold readBlob
    rw [readString_writeString _ _ (by decide : algEd25519.length < 2 ^ 32),
      bind_some_apply]
    dsimp only
    have h2 : readString (writeString key) = some (key, []) := by
      have h3 := readString_writeString key []
        (by rw [hk]; decide : key.length < 2 ^ 32)
      rwa [List.append_nil] at h3
    rw [if_pos rfl, h2, bind_some_apply]
    dsimp only
    rw [if_pos (by simp [hk] :
      (([] : List UInt8).isEmpty && key.length = 32) = true)]
  | rsa e n =>
    have he : 0 < e := hb.1
    have hn : 0 < n := hb.2.1
    have hle : (mpintBytes e).length < 2 ^ 32 := hb.2.2.1
    have hln : (mpintBytes n).length < 2 ^ 32 := hb.2.2.2
    show readBlob (writeString algRsa ++ writeMpint e ++ writeMpint n) =
      some (KeyBlob.rsa e n)
    unfold readBlob
    rw [List.append_assoc,
      readString_writeString _ _ (by decide : algRsa.length < 2 ^ 32),
      bind_some_apply]
    dsimp only
    have h2 : readMpint (writeMpint n) = some (n, []) := by
      have h3 := readMpint_writeMpint n [] hln
      rwa [List.append_nil] at h3
    rw [if_neg (by decide : ¬ algRsa = algEd25519), if_pos rfl,
      readMpint_writeMpint _ _ hle, bind_some_apply]
    dsimp only
    rw [h2, bind_some_apply]
    dsimp only
    rw [if_pos (by simp [he, hn] :
      (([] : List UInt8).isEmpty && (0 < e) && (0 < n)) = true)]

end Ssh.Proofs
