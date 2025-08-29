import Mathlib

-- a Char may represent a bit if this predicate is true
def bitP (c: Char): Prop := c = '0' ∨ c = '1'

-- a Bit is a Char, which is provably equal to 0 or 1
def Bit := {c: Char // bitP c}

-- Bit for 1
def oneB: Bit := ⟨'1',
  by
    right
    rfl
  ⟩

-- Bit for 0
def zeroB : Bit := ⟨'0',
  by
    left
    rfl
  ⟩

-- ) and 1 bits are different as `Bit`s
theorem oneBneZeroB: oneB ≠ zeroB := by
  rw [oneB.eq_def, zeroB.eq_def]
  rw [← Subtype.coe_ne_coe]
  simp

-- We prove every bit is one of the above defined values
theorem bitIsOneBorZeroB (b: Bit): b = zeroB ∨ b = oneB := by
  have h: b.val = '0' ∨ b.val = '1' := by exact Subtype.property b
  cases h with
    | inl h1 =>
      left
      apply Subtype.ext
      rw [zeroB, h1]
    | inr h2 =>
      right
      apply Subtype.ext
      rw [oneB, h2]

instance: DecidableEq Bit := Subtype.instDecidableEq

theorem oneIfNotZero (b: Bit): b ≠ zeroB ↔ b = oneB := by
  have h:= bitIsOneBorZeroB b
  have hh := oneBneZeroB
  cases h
  case inl isZero =>
    rw [isZero]
    tauto
  case inr isOne =>
    rw [isOne]
    tauto


-- 0 and 1 are enforced at the subtype level, bigNat is just a list of bits
def BigNat := List Bit

-- We prove the leading element of a list is one of the two bit constants
theorem headOneOrZero (n: BigNat) (nonzero: n ≠ []) :
  n.head (nonzero) = zeroB ∨ n.head (nonzero) = oneB :=
    bitIsOneBorZeroB (n.head nonzero)

-- Some useful constants
def one: BigNat := List.singleton oneB
def zero: BigNat := []

-- True iff no leading 0s
def isCanonical: BigNat → Prop
  | []  => true
  | h :: _ => h = oneB

-- We prove that zero is represented canonically
theorem zeroIsCanonical: isCanonical zero := by
  rw [isCanonical.eq_def, zero.eq_def]

-- We prove that every list starting with 1 is canonical
theorem head1ListIsCanonical (n: BigNat) (nonzero: n ≠ []) :
  (n.head (nonzero)).val = '1' → isCanonical n := by
    rw [isCanonical.eq_def]
    split
    case h_1 => simp
    case h_2 h t =>
      simp
      intro valOne
      apply Subtype.ext
      rw [valOne, oneB.eq_def]

-- Remove leading 0s
def canonize (n: BigNat): BigNat :=
  match n with
  | [] => zero
  | h :: t => if (h.val = '1') then n else canonize t

-- We prove canonizing results in canonical representations (as expected)
theorem canonizedIsCanonical {n: BigNat}: isCanonical (canonize n) := by
  rw [canonize.eq_def, zero.eq_def]
  induction n
  case nil => trivial
  case cons head tail ih =>
    split
    case h_1 => trivial
    case h_2 a hh tt lsteq =>
      split
      case isTrue e =>
        rw [lsteq]
        apply head1ListIsCanonical
        simp
        exact e
        apply List.cons_ne_nil
      case isFalse e =>
        have sameH: tt = tail := by
          rw [List.cons_eq_cons] at lsteq
          symm
          exact And.right lsteq
        rw [sameH, canonize.eq_def]
        exact ih

-- Helper functions, convert chars/bits to their respective integers
def charConvert (c: Char): Nat :=
  if (c = '1')
  then 1
  else 0

def natFromBit (b: Bit) : Nat := charConvert b.val

-- "reverse" multiplication. Assuming n represents the bits of some natural N
-- _in reverse order_, we compute n by as series of *2 multiplications
def str2natAux (n: BigNat): Nat :=
  match n with
  | [] => 0
  | h :: t => natFromBit h + 2 * (str2natAux t)

-- Convert a BigNat string to its numerical representation.
def str2nat (b: BigNat): Nat :=
  -- We reverse b once and use the str2natAux algorithm
  str2natAux b.reverse

-- A few quick tests
#check str2nat [oneB, zeroB, oneB] = 5
#check str2nat [oneB, oneB, zeroB] = 6
#check str2nat [zeroB, zeroB, oneB, oneB] = 3 -- non canon

-- Inverse operation to natFromBit
def bitFromNat (n: Nat): Bit :=
  if (n = 1)
  then oneB
  else zeroB

-- Constructs the binary representation of n in reverse order
def nat2strAux (n: Nat): BigNat :=
  if (n = 0)
  then zero
  else (bitFromNat (n % 2)) :: nat2strAux (n / 2)

def nat2str (n: Nat): BigNat :=
  -- we use nat2strAux to get the bits in the inverted order, then reverse the result
  (nat2strAux n).reverse

--------------
--  LEMMAS  --
--------------

--------- Zero/one identities ---------

lemma nat2str_0_is_zero: (nat2str 0) = zero := by
  rw [nat2str.eq_def, nat2strAux.eq_def, zero.eq_def]
  simp

-- `zero` and [] are slightly different, syntactically
lemma str2nat_empty_is_0: (str2nat []) = 0 := by
  rw [str2nat.eq_def, str2natAux.eq_def]
  simp

lemma str2nat_zero_is_0: (str2nat zero) = 0 := by
  have h := str2nat_empty_is_0
  tauto

lemma str2nat_one_is_1: (str2nat one) = 1 := by
  tauto

lemma natFromBit_zeroB_is_0: natFromBit zeroB = 0 := by
  rw [zeroB.eq_def, natFromBit.eq_def, charConvert.eq_def]
  simp

lemma natFromBit_oneB_is_1: natFromBit oneB = 1 := by
  rw [oneB.eq_def, natFromBit.eq_def, charConvert.eq_def]
  simp

------------------

--------- Basic arithmetic identities for /, %, etc. ---------

-- auxiliary induction lemma
lemma half_is_smaller (n: Nat): (n + 1) / 2 < n + 1 := by
  have h:= Nat.even_or_odd (n + 1)
  have lt02: 0 < 2 := by simp +arith
  rw [← Nat.mul_lt_mul_left lt02]
  cases h
  case inl h =>
    rw [Nat.two_mul_div_two_of_even]
    simp +arith
    exact h
  case inr h =>
    rw [Nat.two_mul_odd_div_two]
    simp +arith
    rw [Nat.odd_iff] at h
    exact h

-- or-introduction for mod 2 case splitting
lemma mod2_is_0_or_1 (n: Nat): (n % 2 = 0) ∨ (n % 2 = 1) := by
  induction n
  case zero =>
    left
    simp
  case succ n ih =>
    cases ih
    case inl h =>
      right
      rw [Nat.add_mod_eq_sub, h]
      simp
    case inr h =>
      left
      rw [Nat.add_mod_eq_sub, h]
      simp

-- Rounding lemma for induction
lemma div2_rounding (k: Nat): (1 + 2 * k) / 2 = k := by
  have isOdd: Odd (2 * k + 1) := by simp
  apply Nat.one_add_div_two_mul_two_of_odd at isOdd
  simp +arith at isOdd
  simp +arith
  exact isOdd

-- didn't end up needing these, were used in some proof attempts
lemma _leTimesDiv (k: Nat): 2 * (k /2) ≤ k := by
  exact Nat.mul_div_le k 2

lemma _modAsExists {k l: Nat} (modEq: k % 2 = l): ∃q: Nat,  k = 2 * q + l := by
  use (k/2)
  rw [← modEq, Nat.add_comm]
  have h:= _leTimesDiv k
  have hh: k - 2 * (k/2) = k % 2 := by rw [Nat.mod_def]
  apply Nat.sub_eq_iff_eq_add at h
  tauto

------------------

--------- Helper function lemmas ---------

-- Inversion lemmas for bit functions
lemma bitFromNat_natFromBit_inverse (b: Bit): bitFromNat (natFromBit b) = b := by
  have h := bitIsOneBorZeroB b
  rw [natFromBit.eq_def, charConvert.eq_def, bitFromNat.eq_def]
  repeat rw [zeroB.eq_def]
  repeat rw [oneB.eq_def]
  cases h
  case inl hh =>
    rw [hh, zeroB]
    simp
  case inr hh =>
    rw [hh, oneB]
    simp

lemma natFromBit_bitFromNat_inverse {n: Nat} (zeroOrOne: n = 0 ∨ n = 1): natFromBit (bitFromNat n) = n := by
  rw [bitFromNat.eq_def]
  repeat rw [zeroB.eq_def]
  repeat rw [oneB.eq_def]
  cases zeroOrOne
  case inl hh =>
    rw [hh]
    simp
    rw [natFromBit.eq_def, charConvert.eq_def]
    simp
  case inr hh =>
    rw [hh]
    simp
    rw [natFromBit.eq_def, charConvert.eq_def]
    simp

-- natFromBit b = 0 ↔ b = 0
lemma natFromBit_0_only_for_zero {b: Bit} (isZero: natFromBit b = 0): b = zeroB := by
  rw [zeroB]
  rw [natFromBit.eq_def, charConvert.eq_def] at isZero
  rw [ite_eq_right_iff] at isZero
  have h:= bitIsOneBorZeroB b
  cases h
  case inl is0 =>
    tauto
  case inr is1 =>
    rw [oneB.eq_def] at is1
    rw [is1] at isZero
    tauto

-- canonizing a 0-lead representation is the same as canonizing just the tail
lemma canonize_ignores_leading_zeros {t: BigNat} : canonize (zeroB :: t) = canonize t := by
  rw [canonize.eq_def, zeroB.eq_def]
  simp

-- canonizing a canonical value does nothing
lemma canonize_is_identity_on_canonical {t: BigNat} (isCan : isCanonical t) : canonize t = t := by
  cases t
  case nil =>
    rw[canonize.eq_def, zero.eq_def]
  case cons h t =>
    rw [isCanonical.eq_def] at isCan
    simp at isCan
    rw [isCan, canonize.eq_def]
    simp
    tauto

-- str2natAux returns the same value if we append trailing zeros.
-- This is equivalent to str2nat returning the same value for _leading_ zeros
-- (i.e. noncanonical representations of the same nat)
lemma str2natAux_ignores_trailing_zeros (l: BigNat): str2natAux (HAppend.hAppend ↑l [zeroB]) = str2natAux l := by
  induction l
  case nil =>
    repeat rw [str2natAux.eq_def]
    simp
    rw [natFromBit.eq_def, zeroB.eq_def, str2natAux.eq_def, charConvert.eq_def]
    simp
  case cons h t ih =>
    simp
    rw [str2natAux.eq_def]
    simp
    nth_rewrite 2 [str2natAux.eq_def]
    simp
    tauto

-- Corollary of the above lemma
lemma str2nat_ignores_leading_zeros (n: BigNat): str2nat (zeroB :: n) = str2nat n := by
  rw [str2nat.eq_def]
  simp
  rw [str2natAux_ignores_trailing_zeros]
  tauto


-- The head of the list returned by nat2strAux k (whenever k ≠ 0) is k % 2.
-- Therefore, for k = 2n, nat2strAux k has a leading zero bit
lemma nat2strAux_even_prepends_zeroB (n: Nat) (not0: n ≠ 0) : nat2strAux (2 * n) = zeroB :: (nat2strAux n) := by
  rw [nat2strAux.eq_def]
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n
    case zero =>
      tauto
    case succ m =>
      simp +arith
      rw [bitFromNat.eq_def]
      simp

-- Converse of the above, for odd values the returned list has a leading one bit
lemma nat2strAux_odd_prepends_oneB (n: Nat) : nat2strAux (1 + 2 * n) = oneB :: (nat2strAux n) := by
  rw [nat2strAux.eq_def]
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n
    case zero =>
      tauto
    case succ m =>
      simp +arith
      rw [bitFromNat.eq_def]
      simp
      have h : 2 * m + 3 = 1 + 2 * (m +1) := by simp +arith
      rw [h]
      have d2l := div2_rounding (m+1)
      rw [d2l]

-- If a list has a trailing one bit, str2natAux returns a nonzero value
-- (more generally, if _any_ bit is nonzero it returns a nonzero value, but we only
-- need this formulation)
lemma str2natAux_trailing_oneB_is_nonzero (n: BigNat): str2natAux (HAppend.hAppend ↑n [oneB]) ≠ 0 := by
  induction n
  rw [str2natAux.eq_def]
  case nil =>
    simp
    rw [natFromBit.eq_def, charConvert.eq_def]
    simp
    tauto
  case cons h t ih =>
    simp
    rw [str2natAux.eq_def]
    simp
    intro hh
    tauto

------------------

----------------
--  THEOREMS  --
----------------

-- Main result: str2nat and nat2str are inverses (up to canonical representation)

lemma str2natAux_nat2strAux_inverse (n: Nat): str2natAux (nat2strAux n) = n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [str2natAux.eq_def, nat2strAux.eq_def, zero.eq_def]
    cases n
    case _ =>
      simp
    case succ m =>
      have mod2h := mod2_is_0_or_1 m
      simp +arith
      have ltLemma := half_is_smaller m
      apply ih at ltLemma
      rw [ltLemma]
      have mod2h' := mod2_is_0_or_1 (m + 1)
      have nBbNlemma := natFromBit_bitFromNat_inverse mod2h'
      rw [nBbNlemma]
      rw [Nat.mod_add_div]

theorem str2nat_nat2str_inverse (n: Nat): str2nat (nat2str n) = n := by
  rw [nat2str.eq_def, str2nat.eq_def]
  simp
  exact str2natAux_nat2strAux_inverse n

lemma nat2strAux_str2natAux_inverse_on_trailing_oneB (l: BigNat):
  nat2strAux (str2natAux (HAppend.hAppend ↑l [oneB])) = HAppend.hAppend ↑l [oneB] := by
  induction l
  case nil =>
    simp
    rw [str2natAux.eq_def, nat2strAux.eq_def]
    simp
    rw [natFromBit.eq_def]
    repeat rw [oneB.eq_def]
    repeat rw [charConvert.eq_def]
    simp
    rw [str2natAux.eq_def, nat2strAux.eq_def, zero.eq_def, bitFromNat.eq_def, oneB.eq_def]
    simp
  case cons h t ih =>
    rw [str2natAux.eq_def]
    simp
    have zOrO := bitIsOneBorZeroB h
    cases zOrO
    case inl isZero =>
      rw [isZero]
      have str2natAux_trailing_oneB_is_nonzero1 := str2natAux_trailing_oneB_is_nonzero t
      rw [natFromBit_zeroB_is_0]
      rw [Nat.zero_add]
      apply nat2strAux_even_prepends_zeroB at str2natAux_trailing_oneB_is_nonzero1
      rw [str2natAux_trailing_oneB_is_nonzero1]
      rw [ih]

    case inr isOne =>
      rw [isOne]
      rw [natFromBit_oneB_is_1]
      rw [nat2strAux_odd_prepends_oneB]
      rw [ih]

theorem nat2str_str2nat_inverse_up_to_canonical (n: BigNat) : nat2str (str2nat n) = canonize n := by
  rw [nat2str.eq_def, str2nat.eq_def]
  induction n
  case nil =>
    rw [str2natAux.eq_def, nat2strAux.eq_def, canonize.eq_def]
    repeat rw [zero.eq_def]
    simp
  case cons h t ih =>
    have hIs0or1 := bitIsOneBorZeroB h
    cases hIs0or1
    case inl isZero =>
      rw [isZero, canonize_ignores_leading_zeros]
      simp
      have h:= str2natAux_ignores_trailing_zeros t.reverse
      simp at h
      rw [h]
      exact ih
    case inr isOne =>
      rw [isOne]
      simp
      have aux := nat2strAux_str2natAux_inverse_on_trailing_oneB t.reverse
      rw [aux]
      simp
      rw [canonize.eq_def]
      simp
      tauto

------------------

-- str2nat returns the same output for canonical and noncanonical representations of the same n
lemma str2nat_on_canonize_is_str2nat_on_base (n: BigNat): str2nat (canonize n) = str2nat n := by
  induction n
  case nil =>
    rw [canonize.eq_def, zero.eq_def]
  case cons h t ih =>
    have h0or1 := bitIsOneBorZeroB h
    cases h0or1
    case inl isZero =>
      rw [isZero]
      rw [canonize_ignores_leading_zeros, ih]
      rw [str2nat_ignores_leading_zeros]
    case inr isOne =>
      rw [isOne]
      have listIsCanon: isCanonical (oneB :: t) := by tauto
      rw [canonize_is_identity_on_canonical]
      tauto

-- str2natAux can factor out as a sum of powers of 2
lemma str2natAux_is_sum_of_powers_of_2 (b: Bit) (t: BigNat): str2natAux (HAppend.hAppend ↑t [b]) = (natFromBit b) * 2 ^ List.length t + str2natAux t := by
  induction t
  case nil =>
    repeat rw [str2natAux.eq_def]
    simp
    rw [str2natAux.eq_def]
  case cons hd tl ih =>
    rw [str2natAux.eq_def]
    simp
    rw [ih]
    simp +arith
    nth_rewrite 2 [str2natAux.eq_def]
    simp +arith
    rw [Nat.pow_add_one]
    rw [Nat.mul_comm]
    rw [mul_assoc]

-- str2nat can factor out as a sum of powers of 2
lemma str2nat_is_sum_of_powers_of_2 (h: Bit) (t: BigNat): str2nat (h::t) = (natFromBit h) * 2^(t.length) + str2nat t := by
  have h0or1 := bitIsOneBorZeroB h
  cases h0or1
  case inl isZero =>
    rw [isZero]
    rw [str2nat_ignores_leading_zeros, natFromBit_zeroB_is_0]
    simp
  case inr isOne =>
    rw [isOne, natFromBit_oneB_is_1]
    rw [str2nat.eq_def]
    simp
    rw [str2natAux_is_sum_of_powers_of_2 oneB]
    simp +arith
    rw [← str2nat.eq_def]
    simp
    exact natFromBit_oneB_is_1

------------------
--  ARITHMETIC  --
------------------

-- Bit addition functions

-- AKA  b1 != b2  <=> b1 xor b2
def bitAddNoOverflow (b1: Bit) (b2: Bit): Bit :=
  if (b1 = b2)
  then zeroB
  else oneB

-- AKA  b1 = b2 = 1
def bitAddOverflow (b1: Bit) (b2: Bit): Bit :=
  if (b1 = b2 ∧ b1 = oneB)
  then oneB
  else zeroB

-- ¬b
def bitFlip (b: Bit) : Bit := if (b = oneB) then zeroB else oneB

-- ¬0 = 1
lemma bitFlip_zero_is_one: bitFlip zeroB = oneB := by
  rw [bitFlip]
  simp

-- ¬1 = 0
lemma bitFlip_one_is_zero: bitFlip oneB = zeroB := by
  rw [bitFlip]
  simp

-- bitAddNoOverflow a b = bitAddNoOverflow b a
lemma bano_comm (b1: Bit) (b2: Bit): bitAddNoOverflow b1 b2 = bitAddNoOverflow b2 b1 := by
  repeat rw [bitAddNoOverflow.eq_def]
  repeat rw [ite_eq_iff]
  have h1 := bitIsOneBorZeroB b1
  have h2 := bitIsOneBorZeroB b2
  cases h1
  case inl isZero1 =>
    cases h2
    case inl isZero2 =>
      rw [isZero1, isZero2]
      simp
    case inr isOne2 =>
      rw [isZero1, isOne2]
      simp
      tauto
  case inr isOne1 =>
    cases h2
    case inl isZero2 =>
      rw [isOne1, isZero2]
      simp
      tauto
    case inr isOne2 =>
      rw [isOne1, isOne2]
      simp

-- bitAddOverflow a b = bitAddOverflow b a
lemma bao_comm (b1: Bit) (b2: Bit): bitAddOverflow b1 b2 = bitAddOverflow b2 b1 := by
  repeat rw [bitAddOverflow.eq_def]
  repeat rw [ite_eq_iff]
  have h1 := bitIsOneBorZeroB b1
  have h2 := bitIsOneBorZeroB b2
  cases h1
  case inl isZero1 =>
    cases h2
    case inl isZero2 =>
      rw [isZero1, isZero2]
      simp
      tauto
    case inr isOne2 =>
      rw [isZero1, isOne2]
      simp
      tauto
  case inr isOne1 =>
    cases h2
    case inl isZero2 =>
      rw [isOne1, isZero2]
      simp
      tauto
    case inr isOne2 =>
      rw [isOne1, isOne2]
      simp


-- bitAddNoOverflow b 0 = b
lemma bano_b_zero (b: Bit): bitAddNoOverflow b zeroB = b := by
  rw [bitAddNoOverflow.eq_def]
  rw [ite_eq_iff]
  have h := bitIsOneBorZeroB b
  tauto

-- bitAddNoOverflow 0 b = b
lemma bano_zero_b (b: Bit): bitAddNoOverflow zeroB b = b := by
  have h := (bano_b_zero b)
  rw [bano_comm] at h
  exact h

-- bitAddNoOverflow b 1 = ¬b
lemma bano_b_one (b: Bit): bitAddNoOverflow b oneB = bitFlip b := by
  rw [bitAddNoOverflow.eq_def]
  rw [ite_eq_iff]
  have h := bitIsOneBorZeroB b
  cases h
  case inl isZero =>
    rw [isZero]
    rw [bitFlip.eq_def]
    simp
    tauto
  case inr isOne =>
    rw [isOne]
    rw [bitFlip.eq_def]
    simp

-- bitAddNoOverflow 1 b = ¬b
lemma bano_one_b (b: Bit): bitAddNoOverflow oneB b = bitFlip b := by
  have h := (bano_b_one b)
  rw [bano_comm] at h
  exact h

-- bitAddOverflow b 0 = 0
lemma bao_b_zero (b: Bit): bitAddOverflow b zeroB = zeroB := by
  rw [bitAddOverflow.eq_def]
  rw [ite_eq_iff]
  have h := bitIsOneBorZeroB b
  cases h
  case inl isZero =>
    rw [isZero]
    tauto
  case inr isOne =>
    rw [isOne]
    tauto

-- bitAddOverflow 0 b = 0
lemma bao_zero_b (b: Bit): bitAddOverflow zeroB b = zeroB := by
  have h := (bao_b_zero b)
  rw [bao_comm] at h
  exact h

-- bitAddOverflow b 1 = b
lemma bao_b_one (b: Bit): bitAddOverflow b oneB = b := by
  rw [bitAddOverflow.eq_def]
  rw [ite_eq_iff]
  have h := bitIsOneBorZeroB b
  cases h
  case inl isZero =>
    rw [isZero]
    tauto
  case inr isOne =>
    rw [isOne]
    simp

-- bitAddOverflow 1 b = b
lemma bao_one_b (b: Bit): bitAddOverflow oneB b = b := by
  have h := (bao_b_one b)
  rw [bao_comm] at h
  exact h

def sum3Bits (b1: Bit) (b2: Bit) (b3: Bit): Bit :=
  bitAddNoOverflow (bitAddNoOverflow b1 b2) b3
def overflow3Bits (b1: Bit) (b2: Bit) (b3: Bit): Bit :=
  bitAddNoOverflow
    (bitAddOverflow (bitAddNoOverflow b1 b2) b3)
    (bitAddOverflow b1 b2)

-- sum3Bits a b 0 = bitAddNoOverflow a b
lemma sum3_a_b_zero_is_bano_a_b (a: Bit) (b: Bit): sum3Bits a b zeroB = bitAddNoOverflow a b := by
  rw [sum3Bits.eq_def]
  exact bano_b_zero (bitAddNoOverflow a b)

-- sum3Bits b 0 0 = b
lemma sum3_b_zero_zero_is_b (b: Bit): sum3Bits b zeroB zeroB = b := by
  rw [sum3_a_b_zero_is_bano_a_b]
  exact bano_b_zero b

-- sum3Bits 0 b 0 = b
lemma sum3_zero_b_zero_is_b (b: Bit): sum3Bits zeroB b zeroB = b := by
  rw [sum3Bits.eq_def]
  rw [bano_b_zero, bano_zero_b]

-- sum3Bits b 0 1 = ¬b
lemma sum3_b_zero_one_is_flip (b: Bit): sum3Bits b zeroB oneB = bitFlip b := by
  rw [sum3Bits, bano_b_zero, bano_b_one]

-- sum3Bits 0 b 1 = ¬b
lemma sum3_zero_b_one_is_flip (b: Bit): sum3Bits zeroB b oneB = bitFlip b := by
  rw [sum3Bits.eq_def]
  rw [bano_comm zeroB b]
  rw [← sum3Bits.eq_def]
  exact sum3_b_zero_one_is_flip b

-- overflow3Bits a b 0 = bitAddOverflow a b
lemma overflow3_a_b_zero_is_bao_a_b (a: Bit) (b: Bit): overflow3Bits a b zeroB = bitAddOverflow a b:= by
  rw [overflow3Bits.eq_def]
  rw [bao_b_zero, bano_zero_b]

-- overflow3Bits b 0 0 = 0
lemma overflow3_b_zero_zero_is_zero (b: Bit): overflow3Bits b zeroB zeroB = zeroB := by
  rw [overflow3Bits.eq_def]
  rw [bano_b_zero, bao_b_zero, bano_b_zero]

-- overflow3Bits 0 b 0 = 0
lemma overflow3_zero_b_zero_is_zero (b: Bit): overflow3Bits zeroB b zeroB = zeroB := by
  rw [overflow3Bits.eq_def]
  rw [bano_zero_b, bao_b_zero, bano_zero_b, bao_zero_b]

-- overflow3Bits b 0 1 = b
lemma overflow3_b_zero_one_is_b (b: Bit) :
  overflow3Bits b zeroB oneB = b := by
  rw [overflow3Bits, bano_b_zero, bao_b_one, bao_b_zero, bano_b_zero]

-- overflow3Bits 0 b 1 = b
lemma overflow3_zero_b_one_is_b (b: Bit) :
  overflow3Bits zeroB b oneB = b := by
  rw [overflow3Bits, bano_zero_b, bao_b_one, bao_zero_b, bano_b_zero]

-- We perform bitwise addition from the lowest bits upwards
-- so we define a recursive function acting on _reversed_ inputs
def addRecAux (over: Bit) (a:BigNat) (b: BigNat) : BigNat :=
  match a,b with
  | [], [] => [over]
  | ha :: ta, [] => (sum3Bits ha zeroB over) :: addRecAux (overflow3Bits ha zeroB over) ta []
  | [], hb:: tb => (sum3Bits zeroB hb over) :: addRecAux (overflow3Bits zeroB hb over) [] tb
  | ha :: ta, hb :: tb => (sum3Bits ha hb over) :: addRecAux (overflow3Bits ha hb over) ta tb
  termination_by a.length + b.length

-- Bitwise addition
def addRec (a:BigNat) (b: BigNat): BigNat :=
  canonize ((addRecAux zeroB a.reverse b.reverse).reverse)

--------------------

-- Reversing a (h :: t) list is the same as reversing the tail, then appending the head
lemma listReversalLemma (h : Bit) (l: BigNat): (h :: l.reverse) = (HAppend.hAppend ↑l [h]).reverse := by simp

-- a + 0 (carry 0) = a
lemma addRecAux_empty_r (a: BigNat): addRecAux zeroB a [] = HAppend.hAppend ↑a [zeroB] := by
  induction a
  case nil =>
    rw [addRecAux.eq_def]
    simp
  case cons h t ih =>
    rw [addRecAux.eq_def]
    simp
    rw [overflow3_b_zero_zero_is_zero, sum3_b_zero_zero_is_b]
    rw [ih]

-- 0 + a (carry 0) = a
lemma addRecAux_empty_l (a: BigNat): addRecAux zeroB [] a = HAppend.hAppend ↑a [zeroB] := by
  induction a
  case nil =>
    rw [addRecAux.eq_def]
    simp
  case cons h t ih =>
    rw [addRecAux.eq_def]
    simp
    rw [overflow3_zero_b_zero_is_zero, sum3_zero_b_zero_is_b]
    rw [ih]

-- 0 + 0 (carry b) = b
lemma addRecAux_double_empty_is_singleton (o:Bit): addRecAux o [] [] = [o] := by
  rw [addRecAux]

-- a + 0 (carry 1) = (a + 0 (carry 0)) + 1 (carry 0)
lemma addRecAux_over_one_as_over_zero (a: BigNat): HAppend.hAppend ↑(addRecAux oneB a []) [zeroB] = addRecAux zeroB (addRecAux zeroB a []) [oneB]  := by
  induction a
  case nil =>
    rw [addRecAux_double_empty_is_singleton]
    rw [addRecAux_double_empty_is_singleton]
    simp
    rw [addRecAux]
    rw [sum3_zero_b_zero_is_b, overflow3_zero_b_zero_is_zero]
    rw [addRecAux_empty_r]
    simp
  case cons h t ih =>
    rw [addRecAux, sum3_b_zero_one_is_flip, overflow3_b_zero_one_is_b]
    cases t
    case nil =>
      rw [addRecAux_double_empty_is_singleton]
      rw [addRecAux_empty_r]
      rw [addRecAux.eq_def]
      simp
      rw [sum3Bits, bano_b_one, bano_b_zero]
      rw [overflow3Bits, bano_b_one, bao_b_one, bao_b_zero, bano_zero_b]
      rw [addRecAux]
      rw [sum3Bits, bano_b_zero, bano_zero_b, overflow3Bits]
      rw [bano_zero_b, bao_zero_b, bano_zero_b, bao_zero_b]
      rw [addRecAux_double_empty_is_singleton]
      tauto
    case cons hh tt =>
      rw [addRecAux_empty_r]
      have hIs0or1 := bitIsOneBorZeroB h
      cases hIs0or1
      case inl isZero =>
        rw [isZero]
        rw [addRecAux_empty_r]
        rw [addRecAux.eq_def]
        simp
        rw [overflow3_zero_b_zero_is_zero, sum3_zero_b_zero_is_b]
        rw [bitFlip]
        simp
        rw [addRecAux_empty_r]
        simp
      case inr isOne =>
        rw [isOne]
        rw [List.cons_append]
        rw [ih]
        rw [addRecAux_empty_r]
        nth_rewrite 2 [addRecAux.eq_def]
        simp
        rw [bitFlip, sum3_a_b_zero_is_bano_a_b, bano_one_b, bitFlip]
        simp
        rw [overflow3_a_b_zero_is_bao_a_b, bao_b_one]
        rw [addRecAux.eq_def]
        simp
        rw [sum3_a_b_zero_is_bano_a_b, bano_b_one]
        rw [overflow3_a_b_zero_is_bao_a_b, bao_b_one]
        nth_rewrite 2 [addRecAux.eq_def]
        simp
        rw [sum3Bits, bano_b_zero, bano_b_one]
        rw [overflow3Bits, bano_b_zero, bao_b_one, bao_b_zero, bano_b_zero]
        tauto


-- t + 0 (carry b) = t + b (carry 0)
lemma addRecAux_zeroVal_r (o: Bit) (t: BigNat): addRecAux o t [zeroB] = addRecAux zeroB t [o] := by
  induction t generalizing o
  case nil =>
    rw [addRecAux]
    nth_rewrite 2 [addRecAux.eq_def]
    simp
    rw [sum3Bits, bano_zero_b, bano_zero_b, overflow3_zero_b_zero_is_zero, sum3_zero_b_zero_is_b]
    rw [overflow3Bits, bano_zero_b, bao_zero_b, bao_zero_b, bano_zero_b]
  case cons h t ih =>
    rw [addRecAux]
    rw [sum3Bits, bano_b_zero, overflow3Bits, bano_b_zero, bao_b_zero, bano_b_zero]
    nth_rewrite 2 [addRecAux.eq_def]
    simp
    rw [sum3_a_b_zero_is_bano_a_b, overflow3_a_b_zero_is_bao_a_b]

-- a + 0 = a (up to canonize)
lemma addRec_x_zero_is_canonize (x:BigNat) : addRec x [] = canonize x := by
  rw [addRec.eq_def]
  simp
  rw [addRecAux_empty_r]
  simp
  exact canonize_ignores_leading_zeros

-- 0 + a = a (up to canonize)
lemma addRec_zero_x_is_canonize (x:BigNat) : addRec [] x = canonize x := by
  rw [addRec.eq_def]
  simp
  rw [addRecAux_empty_l]
  simp
  exact canonize_ignores_leading_zeros

-- Ended up not needing this
lemma addRecAux_extracts_heads (a: BigNat) (b: BigNat) (ha:Bit) (hb: Bit):
  addRecAux zeroB (ha :: a) (hb :: b) = (bitAddNoOverflow ha hb) :: (addRecAux (bitAddOverflow ha hb) a b) := by
  rw [addRecAux]
  rw [sum3_a_b_zero_is_bano_a_b, overflow3_a_b_zero_is_bao_a_b]

-- '_______b' = 2 * '_______' + b
lemma str2nat_trailingBit (b: Bit) (n: BigNat) : str2nat (HAppend.hAppend ↑n [b]) = natFromBit b + 2 * str2nat n := by
  induction n
  case nil =>
    simp
    rw [str2nat_empty_is_0]
    rw [str2nat, str2natAux.eq_def]
    simp
    exact str2nat_empty_is_0
  case cons h t ih =>
    rw [List.cons_append]
    rw [str2nat_is_sum_of_powers_of_2]
    rw [ih]
    simp +arith
    rw [str2nat_is_sum_of_powers_of_2]
    simp +arith
    rw [Nat.pow_add_one]
    nth_rewrite 2 [Nat.mul_comm]
    repeat rw [← Nat.mul_assoc]
    nth_rewrite 2 [Nat.mul_comm]
    rfl


-- Ended up not needing this
lemma str2nat_addRecAux_reverse_extracts_heads (o: Bit) (h1: Bit) (t1: BigNat) (h2: Bit) (t2:BigNat) :
  str2nat (addRecAux o (h1 :: t1) (h2 :: t2)).reverse = natFromBit (sum3Bits h1 h2 o) + 2 * str2nat (addRecAux (overflow3Bits h1 h2 o) t1 t2).reverse := by
  rw [addRecAux]
  rw [List.reverse_cons]
  rw [str2nat_trailingBit]


-- Ended up not needing this
lemma str2nat_addRecAux_extracts_heads (o: Bit)(a: BigNat) (b: BigNat) (ha:Bit) (hb: Bit):
  str2nat (addRecAux o (ha :: a) (hb :: b)) = (natFromBit (sum3Bits ha hb o)) * 2^((addRecAux (overflow3Bits ha hb o) a b).length) + str2nat (addRecAux (overflow3Bits ha hb o) a b) := by
  induction b generalizing o ha a hb
  case nil =>
    have newOverflow0or1 := bitIsOneBorZeroB (overflow3Bits ha hb o)
    cases newOverflow0or1
    case inl isZero =>
      rw [isZero]
      rw [addRecAux_empty_r]
      rw [addRecAux]
      rw [isZero]
      rw [addRecAux_empty_r]
      rw [str2nat_is_sum_of_powers_of_2]
    case inr isOne =>
      rw [isOne]
      rw [addRecAux]
      rw [str2nat_is_sum_of_powers_of_2]
      simp +arith
      rw [isOne]
  case cons h t ih =>
    rw [addRecAux]
    rw [str2nat_is_sum_of_powers_of_2]

--------- Helper lemmas ---------

-- a + 0 (carry b) = 0 + a (carry b)
lemma addRecAux_comm_zero (o: Bit)(a : BigNat): addRecAux o a [] = addRecAux o [] a := by
  induction a generalizing o
  case nil => rfl
  case cons ha ta ih =>
    rw [addRecAux]
    rw [sum3Bits, bano_b_zero, overflow3Bits, bano_b_zero, bao_b_zero, bano_b_zero]
    cases (bitIsOneBorZeroB ha)
    case inl isZero =>
      rw [isZero]
      rw [bano_zero_b, bao_zero_b]
      rw [addRecAux_empty_r]
      rw [addRecAux]
      rw [sum3Bits, overflow3Bits]
      repeat rw [bano_zero_b, bao_zero_b]
      rw [bano_zero_b]
      rw [addRecAux_empty_l]

    case inr isOne =>
      rw [isOne]
      rw [bao_one_b, bano_one_b]
      have ihInst := ih o
      rw [ihInst]
      nth_rewrite 2 [addRecAux.eq_def]
      simp
      rw [sum3Bits, overflow3Bits]
      repeat rw [bano_zero_b, bao_zero_b, bano_one_b, bao_one_b]
      rw [bano_b_zero]

-- a + 0 (carry 1) = 1 + (a + 0 (carry 0))
lemma plus_one_empty_lemma (l: BigNat): str2nat (addRecAux oneB l.reverse []).reverse = 1 + str2nat (addRecAux zeroB l.reverse []).reverse := by
  rw [addRecAux_empty_r]
  simp
  rw [str2nat_ignores_leading_zeros]
  have doubleRev : str2nat l = str2nat (l.reverse).reverse := by simp
  rw [doubleRev]
  induction l.reverse
  case nil =>
    rw [addRecAux]
    simp
    repeat rw [str2nat]
    simp
    repeat rw [str2natAux]
    rw [natFromBit_oneB_is_1]
  case cons h t ih =>
    rw [addRecAux]
    rw [sum3Bits, overflow3Bits]
    rw [bano_b_zero, bano_b_one, bao_b_zero]
    simp
    rw [str2nat_trailingBit]
    rw [bao_b_one,bano_b_zero]
    cases (bitIsOneBorZeroB h)
    case inl isZero =>
      rw [isZero]
      rw [bitFlip_zero_is_one, natFromBit_oneB_is_1]
      rw [addRecAux_empty_r]
      simp
      rw [str2nat_ignores_leading_zeros, str2nat_trailingBit]
      rw [natFromBit_zeroB_is_0]
      simp
    case inr isOne =>
      rw [isOne]
      rw [ih]
      rw [bitFlip_one_is_zero, natFromBit_zeroB_is_0, str2nat_trailingBit, natFromBit_oneB_is_1]
      simp +arith

-- a + 1 (carry 0) = 1 + a
lemma plus_one_lemma (l: BigNat): str2nat ((addRecAux zeroB l [oneB]).reverse) = 1 + str2nat l.reverse := by
  induction l
  case nil =>
    simp
    rw [addRecAux_empty_l]
    rw [str2nat]
    simp
    rw [str2natAux, str2natAux, str2natAux]
    rw [str2nat_empty_is_0, natFromBit_zeroB_is_0, natFromBit_oneB_is_1]

  case cons h t ih =>
    rw [addRecAux]
    rw [sum3_a_b_zero_is_bano_a_b]
    rw [overflow3_a_b_zero_is_bao_a_b, bano_b_one, bao_b_one]
    cases bitIsOneBorZeroB h
    case inl isZero =>
      rw [isZero]
      rw [addRecAux_empty_r, bitFlip_zero_is_one]
      simp
      rw [str2nat_ignores_leading_zeros]
      repeat rw [str2nat_trailingBit]
      repeat rw [natFromBit_oneB_is_1, natFromBit_zeroB_is_0]
      simp +arith

    case inr isOne =>
      rw [isOne]
      rw [bitFlip_one_is_zero]
      repeat rw [List.reverse_cons]
      repeat rw [str2nat_trailingBit]
      rw [← str2nat_ignores_leading_zeros]
      rw [listReversalLemma]
      rw [addRecAux_over_one_as_over_zero]
      rw [addRecAux_empty_r]
      rw [addRecAux.eq_def]
      split
      case _ err => tauto
      case _ err => tauto
      case _ err _ =>
        apply List.append_ne_nil_of_right_ne_nil at err
        tauto
        tauto
      case h_4 happ tapp hsin tsin consApp consSin =>
        rw [sum3_a_b_zero_is_bano_a_b, overflow3_a_b_zero_is_bao_a_b]
        simp
        rw [str2nat_trailingBit]
        rw [natFromBit_oneB_is_1, natFromBit_zeroB_is_0]
        simp
        rw [List.cons_eq_cons] at consSin
        have hsinIsOne := And.left consSin
        symm at hsinIsOne
        have tsinIsEmpty := And.right consSin
        symm at tsinIsEmpty
        rw [hsinIsOne, tsinIsEmpty]
        rw [bano_b_one, bao_b_one]
        cases (bitIsOneBorZeroB happ)
        case inl isZero =>
          rw [isZero]
          rw [bitFlip_zero_is_one, natFromBit_oneB_is_1]
          rw [addRecAux_empty_r]
          rw [str2nat]
          simp
          rw [str2natAux_ignores_trailing_zeros]
          rw [← str2nat_ignores_leading_zeros]
          have lrl := listReversalLemma zeroB t
          rw [lrl]
          rw [consApp]
          rw [isZero]
          rw [List.reverse_cons]
          rw [str2nat_trailingBit]
          rw [str2nat]
          simp +arith
          exact natFromBit_zeroB_is_0
        case inr isOne =>
          have revConsApp : zeroB :: t.reverse = (happ :: tapp).reverse := by
            rw [listReversalLemma]
            rw [consApp]
          rw [isOne]
          rw [bitFlip_one_is_zero, natFromBit_zeroB_is_0]
          simp
          -- rw [← str2nat_ignores_leading_zeros]
          -- rw [listReversalLemma]
          -- rw [addRecAux_over_one_as_over_zero]
          -- rw [addRecAux_empty_r]

          nth_rewrite 2 [← str2nat_ignores_leading_zeros]
          rw [listReversalLemma]
          rw [consApp]
          rw [isOne]
          rw [List.reverse_cons]
          rw [str2nat_trailingBit]
          rw [natFromBit_oneB_is_1]
          simp +arith
          have ll := plus_one_empty_lemma tapp.reverse
          simp at ll
          rw [ll]
          simp +arith
          rw [addRecAux_empty_r]
          rw [List.reverse_append]
          simp
          exact str2nat_ignores_leading_zeros tapp.reverse

-- a + b (carry 1) = 1 + (a + b (carry 0))
lemma plus_one_general_lemma (a: BigNat) (b:BigNat): str2nat ((addRecAux oneB a b).reverse) = 1 + str2nat ( addRecAux zeroB a b ).reverse := by
  have doubleRev (n: BigNat): n = (n.reverse).reverse := by simp
  rewrite [doubleRev b]
  induction b generalizing a
  case nil =>
    simp
    rewrite [doubleRev a]
    rw [plus_one_empty_lemma]
  case cons hbr tbr ih =>
    cases a
    case nil =>
      simp
      rw [addRecAux_empty_l]
      simp
      rw [str2nat_ignores_leading_zeros]
      rw [← addRecAux_comm_zero]
      rw [addRecAux]
      rw [sum3Bits, overflow3Bits]
      rw [bano_b_zero,bano_b_one,bao_b_one, bao_b_zero, bano_b_zero]
      simp
      repeat rw [str2nat_trailingBit]
      cases (bitIsOneBorZeroB hbr)
      case inl isZero =>
        rw [isZero]
        rw [bitFlip_zero_is_one, natFromBit_oneB_is_1, natFromBit_zeroB_is_0]
        simp +arith
        rw [addRecAux_empty_r]
        rw [List.reverse_append]
        simp
        exact str2nat_ignores_leading_zeros tbr.reverse
      case inr isOne =>
        rw [isOne]
        rw [bitFlip_one_is_zero, natFromBit_oneB_is_1, natFromBit_zeroB_is_0]
        rw [doubleRev tbr]
        rw [plus_one_empty_lemma]
        simp
        rw [addRecAux_empty_r]
        rw [List.reverse_append]
        simp
        rw [str2nat_ignores_leading_zeros]
        simp +arith
    case cons ha ta =>
      simp
      simp at ih
      rw [addRecAux]
      rw [sum3Bits, overflow3Bits]
      rw [bano_b_one,bao_b_one]
      simp
      rw [str2nat_trailingBit]
      nth_rewrite 2 [addRecAux.eq_def]
      simp
      rw [str2nat_trailingBit]
      rw [sum3_a_b_zero_is_bano_a_b, overflow3_a_b_zero_is_bao_a_b]
      cases (bitIsOneBorZeroB ha)
      case inl haIsZero =>
        rw [haIsZero]
        rw [bano_zero_b, bao_zero_b, bano_b_zero]
        cases (bitIsOneBorZeroB hbr)
        case inl hbrIsZero =>
          rw [hbrIsZero]
          rw [bitFlip_zero_is_one, natFromBit_oneB_is_1, natFromBit_zeroB_is_0]
          simp
        case inr hbrIsOne =>
          rw [hbrIsOne]
          rw [bitFlip_one_is_zero, natFromBit_oneB_is_1, natFromBit_zeroB_is_0]
          rw [ih]
          simp +arith

      case inr haIsOne =>
        rw [haIsOne]
        rw [bano_one_b, bao_one_b]
        cases (bitIsOneBorZeroB hbr)
        case inl hbrIsZero =>
          rw [hbrIsZero]
          rw [bitFlip_zero_is_one, bitFlip_one_is_zero, natFromBit_oneB_is_1, natFromBit_zeroB_is_0, bano_b_zero]
          rw [ih]
          simp +arith
        case inr hbrIsOne =>
          rw [hbrIsOne]
          rw [bitFlip_one_is_zero, bitFlip_zero_is_one, natFromBit_oneB_is_1, natFromBit_zeroB_is_0]
          rw [bano_b_one, bitFlip_zero_is_one]
          rw [ih]
          simp +arith

-- a + b (carry o) = o + (a + b (carry 0))
theorem all_sums_over_zero (o: Bit) (a: BigNat) (b: BigNat):
  str2nat (addRecAux o a b).reverse = natFromBit o + str2nat (addRecAux zeroB a b).reverse := by
  cases (bitIsOneBorZeroB o)
  case inl isZero =>
    rw [isZero]
    rw [natFromBit_zeroB_is_0]
    simp
  case inr isOne =>
    rw [isOne]
    rw [natFromBit_oneB_is_1]
    exact plus_one_general_lemma a b

-- Ended up not needing this
lemma oneDir_str2nat_addRecAux_extract_o (h: Bit) (t: BigNat): str2nat (List.reverse (addRecAux oneB [] (h :: t))) = 1 + str2nat (List.reverse (addRecAux zeroB [] (h :: t))) := by
  rw [addRecAux_empty_l]
  rw [addRecAux]
  simp
  rw [overflow3_zero_b_one_is_b, sum3_zero_b_one_is_flip]
  rw [str2nat_trailingBit]
  rw [str2nat_ignores_leading_zeros]
  rw [str2nat_trailingBit]
  cases (bitIsOneBorZeroB h)
  case inl isZero =>
    rw [isZero]
    rw [addRecAux_empty_l]
    rw [bitFlip_zero_is_one, natFromBit_oneB_is_1, natFromBit_zeroB_is_0]
    simp
    exact str2nat_ignores_leading_zeros t.reverse
  case inr isOne =>
    rw [isOne]
    rw [← str2nat_ignores_leading_zeros]
    have rr := listReversalLemma zeroB (addRecAux oneB [] t)
    rw [rr]
    have l := addRecAux_comm_zero oneB t
    rw [← l]
    rw [addRecAux_over_one_as_over_zero]
    rw [addRecAux_empty_r]
    rw [addRecAux.eq_def]
    split
    case _ err => tauto
    case _ err => tauto
    case _ err _ =>
      apply List.append_ne_nil_of_right_ne_nil at err
      tauto
      tauto
    case h_4 happ tapp hsin tsin consApp consSin =>
      rw [sum3_a_b_zero_is_bano_a_b, overflow3_a_b_zero_is_bao_a_b]
      rw [bitFlip_one_is_zero, natFromBit_oneB_is_1, natFromBit_zeroB_is_0]
      simp
      rw [List.cons_eq_cons] at consSin
      have hsinIsOne := And.left consSin
      symm at hsinIsOne
      have tsinIsEmpty := And.right consSin
      symm at tsinIsEmpty
      rw [hsinIsOne, tsinIsEmpty]
      rw [bano_b_one, bao_b_one]
      rw [str2nat_trailingBit]
      cases (bitIsOneBorZeroB happ)
      case inl isZero =>
        rw [isZero]
        rw [bitFlip_zero_is_one, natFromBit_oneB_is_1]
        rw [addRecAux_empty_r]
        rw [str2nat]
        simp
        rw [str2natAux_ignores_trailing_zeros]
        rw [← str2nat_ignores_leading_zeros]
        have lrl := listReversalLemma zeroB t
        rw [lrl]
        rw [consApp]
        rw [isZero]
        rw [List.reverse_cons]
        rw [str2nat_trailingBit]
        rw [str2nat]
        simp +arith
        exact natFromBit_zeroB_is_0
      case inr isOne =>
        rw [isOne]
        rw [bitFlip_one_is_zero, natFromBit_zeroB_is_0]
        rw [← str2nat_ignores_leading_zeros]
        rw [listReversalLemma]
        rw [addRecAux_over_one_as_over_zero]
        rw [addRecAux_empty_r]
        rw [plus_one_lemma]
        rw [← listReversalLemma]
        rw [str2nat_is_sum_of_powers_of_2]
        rw [natFromBit_zeroB_is_0]
        rw [str2nat]
        simp
        rw [← str2nat_ignores_leading_zeros]
        have lrl := listReversalLemma zeroB t
        rw [lrl]
        rw [consApp]
        rw [isOne]
        rw [List.reverse_cons]
        rw [str2nat_trailingBit]
        rw [str2nat]
        simp +arith
        exact natFromBit_oneB_is_1


-- Ended up not needing this
lemma str2nat_addRecAux_extract_o (o: Bit) (a: BigNat) (b: BigNat):
  str2nat ( ( addRecAux o a b ).reverse ) = natFromBit o + str2nat ( ( addRecAux zeroB a b ).reverse ) := by
    have o0or1 := bitIsOneBorZeroB o
    cases o0or1
    case inl isZero =>
      rw [isZero]
      rw [natFromBit_zeroB_is_0]
      simp +arith

    case inr isOne =>
      rw [isOne]
      rw [natFromBit_oneB_is_1]
      cases a
      cases b
      case nil.nil =>
        repeat rw [addRecAux_empty_r]
        rw [addRecAux]
        simp
        repeat rw [str2nat_is_sum_of_powers_of_2]
        repeat rw [str2nat_empty_is_0]
        simp
        rw [natFromBit_oneB_is_1, natFromBit_zeroB_is_0]
      case nil.cons h t =>
        rw [oneDir_str2nat_addRecAux_extract_o]
      case cons ha ta =>
        cases b
        case nil =>
          repeat rw [addRecAux_comm_zero]
          rw [oneDir_str2nat_addRecAux_extract_o]
        case cons hb tb =>
          rw [str2nat_addRecAux_reverse_extracts_heads]
          rw [sum3Bits, overflow3Bits]
          rw [bano_b_one, bao_b_one]
          rw [addRecAux]
          rw [sum3_a_b_zero_is_bano_a_b, overflow3_a_b_zero_is_bao_a_b]
          simp
          rw [str2nat_trailingBit]
          cases (bitIsOneBorZeroB ha)
          case inl haIsZero =>
            cases (bitIsOneBorZeroB hb)
            case inl hbIsZero =>
              rw [haIsZero, hbIsZero]
              rw [bano_zero_b, bao_zero_b, bano_zero_b, bitFlip_zero_is_one, natFromBit_zeroB_is_0, natFromBit_oneB_is_1]
              simp
            case inr hbIsOne =>
              rw [haIsZero, hbIsOne]
              rw [bano_zero_b, bao_zero_b, bano_one_b, bitFlip_one_is_zero, bitFlip_zero_is_one , natFromBit_zeroB_is_0, natFromBit_oneB_is_1]
              simp +arith
              have ll := plus_one_general_lemma ta.reverse.reverse tb.reverse.reverse
              simp at ll
              rw [ll]
              simp +arith
          case inr haIsOne =>
            cases (bitIsOneBorZeroB hb)
            case inl hbIsZero =>
              rw [haIsOne, hbIsZero]
              rw [bano_one_b, bao_one_b, bano_b_zero, bitFlip_zero_is_one, bitFlip_one_is_zero, natFromBit_zeroB_is_0, natFromBit_oneB_is_1]
              simp
              simp +arith
              have ll := plus_one_general_lemma ta.reverse.reverse tb.reverse.reverse
              simp at ll
              rw [ll]
              simp +arith
            case inr hbIsOne =>
              rw [haIsOne, hbIsOne]
              rw [bano_one_b, bitFlip_one_is_zero, bitFlip_zero_is_one, bao_one_b, bano_zero_b,  natFromBit_zeroB_is_0, natFromBit_oneB_is_1]
              simp +arith

-- a' + b' (carry 0) = a' + b'
lemma addRec_equivalent_to_plus_reverse (a: BigNat) (b: BigNat): str2nat (addRec a.reverse b.reverse) = str2nat a.reverse + str2nat b.reverse := by
    rw [addRec]
    rw [str2nat_on_canonize_is_str2nat_on_base]
    induction a generalizing b
    case nil =>
      simp
      rw [addRecAux_empty_l, str2nat_empty_is_0]
      simp
      rw [str2nat_ignores_leading_zeros]

    case cons ha ta ih =>
      simp at ih
      simp
      rw [str2nat_trailingBit]
      cases b
      case nil =>
        rw [addRecAux]
        simp
        rw [sum3_a_b_zero_is_bano_a_b, overflow3_a_b_zero_is_bao_a_b, bano_b_zero, bao_b_zero]
        rw [addRecAux_empty_r]
        simp
        rw [str2nat_ignores_leading_zeros]
        rw [str2nat_trailingBit]
        rw [str2nat_empty_is_0]
        simp
      case cons hb tb =>
        rw [addRecAux]
        rw [sum3_a_b_zero_is_bano_a_b, overflow3_a_b_zero_is_bao_a_b]
        simp
        repeat rw [str2nat_trailingBit]
        rw [all_sums_over_zero]
        rw [ih]
        simp +arith
        cases (bitIsOneBorZeroB ha)
        case inl haIsZero =>
          rw [haIsZero]
          rw [bano_zero_b, bao_zero_b]
          repeat rw [natFromBit_zeroB_is_0]
          simp +arith
        case inr haIsOne =>
          rw [haIsOne]
          rw [bano_one_b, bao_one_b]
          rw [natFromBit_oneB_is_1]
          cases (bitIsOneBorZeroB hb)
          case inl hbIsZero =>
            rw[hbIsZero]
            rw [bitFlip_zero_is_one]
            repeat rw [natFromBit_oneB_is_1, natFromBit_zeroB_is_0]
          case inr hbIsOne =>
            rw[hbIsOne]
            rw [bitFlip_one_is_zero]
            repeat rw [natFromBit_oneB_is_1, natFromBit_zeroB_is_0]

lemma doubleRev (n: BigNat): n = (n.reverse).reverse := by simp

-- a + b (carry 0) = a + b
theorem addRec_equivalent_to_plus (a: BigNat) (b: BigNat): str2nat (addRec a b) = str2nat a + str2nat b := by
  rw [doubleRev a, doubleRev b]
  exact addRec_equivalent_to_plus_reverse a.reverse b.reverse

-------------------------------------------

-- 0b < 1b
def bitLt (b1: Bit) (b2: Bit) := b1 = zeroB ∧ b2 = oneB

-- For two representations padded to the same length we can
-- determine LT by traversing in lockstep
def ltSameLen {a: BigNat} {b: BigNat} (sameLen: a.length = b.length) :=
  match a, b with
  | [], [] => False
  | (ha :: ta), (hb :: tb) =>
    have sameLenTails : ta.length = tb.length := by
      rw [List.length_cons] at sameLen
      rw [List.length_cons] at sameLen
      exact Nat.add_right_cancel sameLen
    (bitLt ha hb) ∨ ltSameLen sameLenTails

-- In general, we need to first pad the shorter representation with 0s
def lt (a: BigNat) (b: BigNat) :=
  let ca := canonize a
  let cb := canonize b
  let la := ca.length
  let lb := cb.length
  let m := max la lb
  let padA := ca.leftpad m zeroB
  let padB := cb.leftpad m zeroB
  have lemm1 : la ≤ m ∧ lb ≤ m := by
    unfold m
    simp
  have lemm2 : padA.length = padB.length := by
    unfold padA padB
    rw [List.length_leftpad]
    rw [List.length_leftpad]
    unfold la lb at lemm1
    have l := And.left lemm1
    have r := And.right lemm1
    rw [Nat.max_eq_left l]
    rw [Nat.max_eq_left r]

  ltSameLen lemm2


theorem lt_is_natLt (a: BigNat) (b: BigNat): (lt a b) = ((str2nat a) < (str2nat b)) := by
  unfold lt
  -- How do I get to the let-s in the proof?
  sorry

-- a < b ↔ canonize a < b
lemma lt_same_on_canonize (a: BigNat) (n: BigNat): lt a n ↔ lt (canonize a) n := by
  repeat rw [lt_is_natLt]
  rw [str2nat_on_canonize_is_str2nat_on_base]


instance (a: BigNat) (b: BigNat): Decidable (lt a b) := by
  rw [lt_is_natLt]
  -- Why is < here deemed not decidable in Nat?
  sorry

-- '____b___' => '____¬b___'
def flipAllBits (a: BigNat) : BigNat :=
  match a with
  | [] => []
  | ( h:: t ) => bitFlip h :: flipAllBits t

-- Prepend 0s. May become noncanonical, but represented value doesn't change
def padToLength (b: BigNat) (l: Nat): BigNat := b.leftpad l zeroB

-- padding + bit flipping
def makeComplement (b: BigNat) (l: Nat) := flipAllBits (padToLength b l)

-- We compute 2s complement "addition", which returns a - b + 2^k
def subAux (a: BigNat) (b: BigNat) := (addRec a (addRec (makeComplement b a.length) one))

-- We trim the leading 1 bit
def sub (a: BigNat) (b: BigNat) := (subAux a b).tail

-- Binary representations of length n cover at most 0..2^n-1
lemma binary_le_2_to_len (a: BigNat) : str2nat (a) < 2^a.length := by
  induction a
  case nil =>
    simp
    exact str2nat_zero_is_0
  case cons h t ih =>
    rw [str2nat_is_sum_of_powers_of_2]
    simp
    have l (k: Nat): 0 < 2^k := by simp
    cases (bitIsOneBorZeroB h)
    case inl isZero =>
      rw [isZero, natFromBit_zeroB_is_0]
      simp
      rw [Nat.pow_add_one]
      rw [Nat.mul_two]
      exact Nat.lt_add_left (2^t.length) ih
    case inr isOne =>
      rw [isOne, natFromBit_oneB_is_1]
      simp
      rw [Nat.pow_add_one]
      rw [Nat.mul_two]
      simp
      exact ih

-- ¬'bb...b' = '¬b¬b...¬b'
lemma flip_replicated_is_replicated_flip (b: Bit) (l: Nat): flipAllBits (List.replicate l b) = List.replicate l (bitFlip b) := by
  induction l generalizing b
  case zero =>
    simp
    rw [flipAllBits]
  case succ n ih =>
    rw [Nat.add_comm]
    repeat rw [← List.replicate_append_replicate]
    rw [List.replicate_one]
    simp
    rw [flipAllBits]
    rw [ih]

-- ¬('___' + '___') = ¬'______'
lemma flip_append_is_append_flip (l: BigNat) (l': BigNat): flipAllBits (List.append l l') = List.append (flipAllBits l) (flipAllBits l') := by
  induction l generalizing l'
  case nil =>
    nth_rewrite 2 [flipAllBits.eq_def]
    simp
  case cons h t ih =>
    have lem: (h :: t).append l' = h :: (t.append l') := by simp
    rw [lem]
    repeat rw [flipAllBits]
    rw [ih]
    exact List.cons_append

-- '11...1' = 2^k -1
lemma str2nat_replicated_ones (k: Nat): str2nat (List.replicate k oneB) + 1 = 2 ^ k := by
  induction k
  case zero =>
    simp
    exact str2nat_empty_is_0
  case succ k' ih =>
    rw [Nat.add_comm k' 1]
    rw [List.replicate_add, List.replicate_one]
    simp
    rw [str2nat_is_sum_of_powers_of_2, natFromBit_oneB_is_1]
    rw [Nat.add_assoc, ih]
    simp +arith
    rw [Nat.pow_add_one']

-- b + ¬b = 2^k - 1 ↔ ¬b + 1 = 2^k - b
lemma complement_adds_to_pow_2_minus_one (b: BigNat) (k: Nat):
  str2nat (makeComplement b k) + 1 = 2^(max k b.length) - str2nat (b) := by
    rw [makeComplement, padToLength]
    rw [doubleRev b]
    induction b.reverse generalizing k
    case nil =>
      simp
      rw [flip_replicated_is_replicated_flip]
      rw [bitFlip_zero_is_one, str2nat_empty_is_0]
      simp
      exact str2nat_replicated_ones k
    case cons h t ih =>
      simp
      rw [← List.append_assoc]
      rw [← List.append_eq]
      rw [flip_append_is_append_flip _ [h]]
      simp
      nth_rewrite 2 [flipAllBits.eq_def]
      simp
      nth_rewrite 2 [flipAllBits.eq_def]
      simp
      rw [str2nat_trailingBit]
      simp at ih
      have ihInst := ih (k-1)
      have sub_add (x: Nat)(y: Nat): x - 1 - y = x - (y + 1) := by
        rw [Nat.sub_right_comm]
        rw [Nat.sub_add_eq]
      rw [sub_add] at ihInst
      have plus_one (x: Nat) (y: Nat): x = y ↔ x + 1 = y + 1 := by simp
      rw [plus_one]
      have two : 1 + 1 = 2 := by simp
      repeat rw [Nat.add_assoc]
      rw [two]
      nth_rewrite 2 [← Nat.mul_one 2]
      rw [← Nat.mul_add]
      rw [ihInst]
      rw [Nat.mul_sub]
      rw [← Nat.pow_add_one']
      rw [str2nat_trailingBit]
      rw [Nat.add_comm]
      cases (bitIsOneBorZeroB h)
      case inl isZero =>
        rw [isZero, bitFlip_zero_is_one, natFromBit_oneB_is_1, natFromBit_zeroB_is_0]
        simp
        cases k
        case zero =>
          simp
        case succ k' =>
          simp
      case inr isOne =>
        rw [isOne, bitFlip_one_is_zero, natFromBit_oneB_is_1, natFromBit_zeroB_is_0]
        simp +arith
        rw [Nat.sub_add_eq]

        have h : (max (k - 1) t.length) + 1 = max k (t.length + 1) := by
          cases k
          case zero =>
            simp
          case succ k' =>
            simp
        rw [h]

        rw [Nat.sub_add_cancel]
        -- + goal
        have l:= binary_le_2_to_len t.reverse
        simp at l
        have ll := Nat.le_max_right k (t.length + 1)
        have one_le_2 : 1 < 2 := by simp
        have ll' : 2^(t.length +1) ≤ 2^(max k (t.length + 1)) := by
          apply Nat.pow_le_pow_iff_right at one_le_2
          rw [one_le_2]
          exact ll
        have lll : 2 * str2nat t.reverse < 2 ^ (t.length +1) := by
          rw [Nat.pow_add_one']
          simp
          exact l
        have lll': 1 + 2 * str2nat t.reverse < 1 + 2 ^ (t.length +1) := by
          simp
          exact lll
        have l' (x y z: Nat) : (x ≤ y - z) = (x + z ≤ y - z + z) := by simp +arith
        rw [l']
        nth_rewrite 2 [Nat.add_comm] at lll'
        rw [← Nat.le_iff_lt_add_one] at lll'
        rw [Nat.sub_add_cancel] -- + goal
        exact Nat.le_trans (lll') (ll')
        ---
        apply Nat.le_of_lt at lll
        exact Nat.le_trans (lll) (ll')


-- Leading bit of 2s complement is 1
lemma subAux_head_one (a: BigNat) (b: BigNat) (leB: ¬(lt a b)): ∃t: BigNat, subAux a b = oneB :: t := by
  -- out of time
  sorry

lemma subAux_max_len_plus_one (a: BigNat) (b: BigNat) (leB: ¬(lt a b)):
  List.length (subAux a b) = (max a.length b.length) + 1 :=
    -- out of time
    by sorry


-- b ≤ a → sub a b = a - b
theorem sub_is_minus (a: BigNat) (b: BigNat) (leB: ¬(lt a b)):
  str2nat (sub a b) = str2nat a - str2nat b:= by
    have h:= (subAux_head_one a b) leB
    cases h
    case intro t isTail =>
      rw [sub]
      have h: str2nat (subAux a b).tail = str2nat (subAux a b) - 2^((subAux a b).tail.length) := by
        rw [isTail]
        simp
        rw [str2nat_is_sum_of_powers_of_2, natFromBit_oneB_is_1]
        simp +arith
      rw [h]
      nth_rewrite 1 [subAux]
      repeat rw [addRec_equivalent_to_plus]
      rw [str2nat_one_is_1]
      have l := complement_adds_to_pow_2_minus_one b (List.length a)
      rw [l]
      simp
      rw [subAux_max_len_plus_one]
      simp
      rw [← Nat.add_sub_assoc] -- new goal
      rw [← Nat.sub_right_comm]
      simp
      ---
      have h' := binary_le_2_to_len b
      have hh := Nat.le_max_right a.length b.length
      have two_gt_0 : 2 > 0 := by simp
      have hh' := Nat.pow_le_pow_right two_gt_0 hh
      apply Nat.le_of_lt at h'
      exact Nat.le_trans h' hh'
      exact leB


-- a => a'0...0' (= _ << k)
def shiftLeft (k: Nat) (a: BigNat): BigNat := List.append a (List.replicate k zeroB)

-- a ++ b = a * 2^k + b
lemma str2nat_concat (a: BigNat) (b: BigNat): str2nat (List.append a b) = str2nat (a) * 2^(b.length) +  str2nat b := by
  induction a
  case nil =>
    simp
    exact str2nat_empty_is_0
  case cons h t ih =>
    simp
    repeat rw [str2nat_is_sum_of_powers_of_2]
    simp +arith
    rw [List.append_eq] at ih
    rw [ih]
    rw [Nat.add_comm (str2nat t * 2 ^ List.length b) (str2nat b)]
    simp +arith
    rw [Nat.pow_add]
    rw [Nat.add_mul]
    rw [Nat.mul_comm (2 ^ List.length b)  (2 ^ t.length)]
    simp +arith
    rw [Nat.mul_assoc]

-- a << 0 = a
lemma shiftLeft_0_is_id (a: BigNat): shiftLeft 0 a = a := by
  rw [shiftLeft]
  rw [List.replicate_zero]
  rw [List.append_eq]
  rw [List.append_nil]

-- a << k + 1 = (a << k) ++ '0'
lemma shiftLeft_plus_one_adds_zero (n: Nat) (a: BigNat): (shiftLeft (n + 1) a) = List.append (shiftLeft n a) [zeroB] := by
  induction n generalizing a
  case zero =>
    simp
    rw [shiftLeft_0_is_id]
    rw [shiftLeft]
    rw [List.append_eq]
    simp
  case succ k ih =>
    rw [ih]
    simp
    rw [shiftLeft]
    rw [List.replicate_add]
    rw [List.replicate_add]
    rw [shiftLeft]
    simp

-- a << k = a * 2^k
lemma shiftLeft_is_mul_by_pow_of_2 (k: Nat) (a: BigNat): str2nat (shiftLeft k a) = (str2nat a) * 2^k := by
  induction k generalizing a
  case zero =>
    rw [shiftLeft_0_is_id]
    simp
  case succ n ih =>
    rw [shiftLeft_plus_one_adds_zero]
    rw [List.append_eq]
    rw [str2nat_trailingBit]
    rw [ih]
    rw [natFromBit_zeroB_is_0]
    simp +arith
    rw [← Nat.mul_assoc]
    rw [Nat.mul_comm 2 _]
    rw [Nat.pow_add_one']
    rw [Nat.mul_assoc]

-- a * (2^k δ + b') =  (a << k)δ + a * b'
def mulAux (a: BigNat) (b: BigNat) : BigNat :=
  match b with
  | [] => []
  | h :: t =>
    let tMul := mulAux a t
    if (h = zeroB) then tMul else addRec ( shiftLeft (t.length) a ) (tMul)

def mul (a: BigNat) (b: BigNat) : BigNat := canonize (mulAux a b)

-- mul a b = a * b
theorem mul_is_times (a: BigNat) (b: BigNat): str2nat (mul a b) = (str2nat a) * (str2nat b) := by
  rw [mul]
  rw [str2nat_on_canonize_is_str2nat_on_base]
  induction b generalizing a
  case nil =>
    rw [mulAux]
    rw [str2nat_empty_is_0]
    simp
  case cons hb tb ih =>
    cases (bitIsOneBorZeroB hb)
    case inl isZero =>
      rw [mulAux]
      rw [isZero]
      simp
      rw [ih]
      rw [str2nat_ignores_leading_zeros]
    case inr isOne =>
      rw [isOne]
      rw [str2nat_is_sum_of_powers_of_2]
      rw [natFromBit_oneB_is_1]
      simp
      rw [mulAux]
      have l: (oneB = zeroB) = False := by
        rw [oneB, zeroB]
        rw [Subtype.eq_iff]
        simp
      rw [ite_cond_eq_false (mulAux a tb) (addRec (shiftLeft tb.length a) (mulAux a tb)) l]
      rw [addRec_equivalent_to_plus]
      rw [shiftLeft_is_mul_by_pow_of_2]
      rw [ih]
      rw [← Nat.mul_add]

-- a % n = if (a < n) then a else (a-n) % n (for n > 0)
def modAux (a: BigNat) (n: BigNat) (nPositive : 0 < str2nat n): BigNat :=
  if (lt a n)
  then canonize a
  else modAux (sub (canonize a) n) n nPositive
  termination_by str2nat (canonize a)
  decreasing_by
    -- How do I reference the if-branch condition ¬lt a n ?
    -- it shows as h✝ but I don't know the syntax to bind it.
    have ifCond: ¬lt a n := by sorry --workaround: introduce manually
    rw [lt_same_on_canonize] at ifCond
    have l := sub_is_minus (canonize a) n ifCond
    rw [str2nat_on_canonize_is_str2nat_on_base]
    rw [l]
    rw [lt_is_natLt] at ifCond
    simp at ifCond
    have aGe0 : 0 < str2nat (canonize a) := by
      rw [Nat.lt_iff_add_one_le] at nPositive
      simp at nPositive
      have ll := Nat.le_trans nPositive ifCond
      rw [Nat.lt_iff_add_one_le]
      simp
      exact ll
    apply Nat.sub_add_cancel at ifCond
    exact Nat.sub_lt aGe0 nPositive

-- (canonize a) % n = a % n
lemma modAux_same_on_canonize (a: BigNat) (n: BigNat) (nPositive : 0 < str2nat n):
  modAux (canonize a) n nPositive = modAux a n nPositive := by
    rw [modAux]
    have l := lt_same_on_canonize a n
    -- I don't know how to rewrite (p <=> q) -> ∀a,b: ITE p a b = ITE q a b
    rw [ite_eq_iff]
    rw [← l]
    rw [← ite_eq_iff]
    nth_rewrite 2 [modAux]
    rw [canonize_is_identity_on_canonical]
    exact canonizedIsCanonical

-- a % n
def mod (a: BigNat) (n: BigNat) (nPositive : 0 < str2nat n): BigNat :=
  -- Add in extra canonizes so we can use nat2str <-> str2nat inversion
  -- and do strong induction on Nats
  modAux (canonize a) n nPositive

-- mod a n = a % n
theorem mod_is_percent (a: BigNat) (n: BigNat) (nPositive : 0 < str2nat n):
  str2nat (mod a n nPositive) = str2nat a % (str2nat n) := by
  rw [mod]
  rw [← nat2str_str2nat_inverse_up_to_canonical]

  induction (str2nat a) using Nat.strong_induction_on with
    | h n ih =>
      cases n
      case zero =>
        rw [nat2str_0_is_zero, zero]
        simp
        rw [modAux.eq_def]
        have l : lt [] n = True := by
          rw [lt_is_natLt]
          rw [str2nat_empty_is_0]
          exact eq_true nPositive
        rw [ite_cond_eq_true _ _ l]
        exact str2nat_empty_is_0
      case succ m =>
        rw [modAux]
        split
        case isTrue ifCond =>
          rw [str2nat_on_canonize_is_str2nat_on_base]
          rw [str2nat_nat2str_inverse]
          rw [Nat.mod_eq_of_lt]
          rw [lt_is_natLt] at ifCond
          rw [str2nat_nat2str_inverse] at ifCond
          exact ifCond
        case isFalse ifCond =>
          have ifCond':= ifCond
          rw [lt_is_natLt] at ifCond
          rw [str2nat_nat2str_inverse] at ifCond
          simp at ifCond
          have l : (str2nat (sub (canonize (nat2str (m + 1))) n)) < m + 1 := by
            have ll:= sub_is_minus (canonize (nat2str (m + 1))) n
            rw [← lt_same_on_canonize] at ll
            apply ll at ifCond'
            rw [ifCond']
            rw [str2nat_on_canonize_is_str2nat_on_base]
            rw [str2nat_nat2str_inverse]
            simp +arith
            exact nPositive
          have ihInst := ih (str2nat (sub (canonize (nat2str (m + 1))) n))

          apply ihInst at l
          rw [nat2str_str2nat_inverse_up_to_canonical] at l
          rw [modAux_same_on_canonize] at l
          rw [l]
          rw [sub_is_minus]
          rw [str2nat_on_canonize_is_str2nat_on_base]
          rw [str2nat_nat2str_inverse]
          rw [← Nat.mod_eq_sub_mod]
          simp
          exact ifCond
          rw[← lt_same_on_canonize]
          exact ifCond'


-- (a + b) % n
def modAdd (a: BigNat) (b: BigNat) (n: BigNat) (nPositive : 0 < str2nat n): BigNat :=
  mod (addRec a b) n nPositive

-- modAdd a b n = (a + b) % n
def modAdd_is_plus_percent (a: BigNat) (b: BigNat) (n: BigNat) (nPositive : 0 < str2nat n):
  str2nat (modAdd a b n nPositive) = ((str2nat a) + (str2nat b)) % (str2nat n) := by
    rw [modAdd]
    rw [mod_is_percent]
    rw [addRec_equivalent_to_plus]

-- (a * b) % n
def modMul (a: BigNat) (b: BigNat) (n: BigNat) (nPositive : 0 < str2nat n): BigNat :=
  mod (mul a b) n nPositive

-- modMul a b n = (a * b) % n
def modMul_is_times_percent (a: BigNat) (b: BigNat) (n: BigNat) (nPositive : 0 < str2nat n):
  str2nat (modMul a b n nPositive) = ((str2nat a) * (str2nat b)) % (str2nat n) := by
    rw [modMul]
    rw [mod_is_percent]
    rw [mul_is_times]

-- a => a^2
def square (a: BigNat): BigNat := mul a a

-- square a = a^2
lemma square_is_pow_2 (a: BigNat): str2nat (square a) = (str2nat a) ^ 2 := by
  rw [square]
  rw [mul_is_times]
  rw [← Nat.pow_two]

-- a^(2^k + b) = a^(2^k) * a^b
-- a^2^k = (a^(2^(k-1))^2
def expAux (coef: BigNat) (revExp: BigNat): BigNat:=
  match revExp with
  | [] => [oneB]
  | h :: t =>
    let tailMul := expAux (square coef) t
    if (h = zeroB)
    then tailMul
    else mul coef tailMul

-- a ^ b
def exp (a: BigNat) (b: BigNat): BigNat :=
  expAux a (b.reverse)

-- exp a b = a ^ b
theorem exp_is_pow (a: BigNat) (b: BigNat): str2nat (exp a b) = (str2nat a) ^ (str2nat b) := by
  rw [doubleRev b]
  rw [exp]
  rw [← doubleRev]
  induction b.reverse generalizing a
  case nil =>
    simp
    rw [str2nat_empty_is_0]
    rw [expAux]
    rw [str2nat]
    simp
    rw [str2natAux]
    rw [str2natAux]
    rw [natFromBit_oneB_is_1]
    simp
  case cons hb tb ih =>
    simp
    rw [str2nat_trailingBit]
    rw [expAux]
    cases (bitIsOneBorZeroB hb)
    case inl isZero =>
      rw [isZero]
      rw [natFromBit_zeroB_is_0]
      simp +arith
      rw [ih]
      rw [square_is_pow_2]
      rw [← Nat.pow_mul]
    case inr isOne =>
      rw [isOne]
      rw [natFromBit_oneB_is_1]
      have l: (oneB = zeroB) = False := by
        rw [oneB, zeroB]
        rw [Subtype.eq_iff]
        simp
      rw [ite_cond_eq_false _ _ l]
      rw [mul_is_times]
      rw [ih]
      rw [square_is_pow_2]
      rw [← Nat.pow_mul]
      rw [Nat.add_comm]
      rw [Nat.pow_add_one']

-- (a ^ b) % n
def modExp (a: BigNat) (b: BigNat) (n: BigNat) (nPositive : 0 < str2nat n): BigNat :=
  mod (exp a b) n nPositive

-- modExp a b n = (a ^ b) % n
theorem modExp_is_pow_percent (a: BigNat) (b: BigNat) (n: BigNat) (nPositive : 0 < str2nat n):
  str2nat (modExp a b n nPositive) = ((str2nat a)^(str2nat b)) % str2nat n := by
    rw [modExp]
    rw [mod_is_percent]
    rw [exp_is_pow]
