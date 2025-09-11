namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

def Exp_int (x y : Nat) : Nat :=
  if y = 0 then 1 else x * Exp_int x (y - 1)

def AllZero (s : String) : Prop :=
  ∀ i, s.get? i = some '0'

def Mul (s1 s2 : String) : String :=
  sorry

axiom Mul_spec (s1 s2 : String) (h1 : ValidBitString s1) (h2 : ValidBitString s2) :
  ValidBitString (Mul s1 s2) ∧ Str2Int (Mul s1 s2) = Str2Int s1 * Str2Int s2

def Zeros (n : Nat) : String :=
  sorry

axiom Zeros_spec (n : Nat) :
  let s := Zeros n
  s.length = n ∧ ValidBitString s ∧ Str2Int s = 0 ∧ AllZero s

-- <vc-helpers>
-- LLM HELPER
open List

-- build the binary digit list (most-significant-bit first)
partial def bits_of_nat : Nat -> List Char
| 0 => []
| n =>
  let q := n / 2
  let r := n % 2
  bits_of_nat q ++ [if r = 1 then '1' else '0']
termination_by bits_of_nat _ => _
-- LLM HELPER

-- LLM HELPER
def Nat_to_bin (n : Nat) : String :=
  if n = 0 then "0" else String.mk (bits_of_nat n)
-- LLM HELPER

-- LLM HELPER
theorem bits_of_nat_correct (n : Nat) :
  (bits_of_nat n).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 = n := by
  -- strong induction on n because recursive call uses n / 2
  apply Nat.strong_induction_on n
  intro k ih
  cases k with
  | zero => simp [bits_of_nat]
  | succ k' =>
    let m := k'.succ
    dsimp [bits_of_nat]
    let q := m / 2
    let r := m % 2
    -- q < m, so we can apply IH
    have qlt : q < m := by
      -- handle small cases explicitly
      cases k' with
      | zero => simp [q]; norm_num
      | succ _ => apply Nat.div_lt_self; linarith
    have ihq := ih q qlt
    -- foldl over append: foldl f 0 (l ++ [c]) = f (foldl f 0 l) c
    have : (bits_of_nat q ++ [if r = 1 then '1' else '0'])
            .foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0
          = 2 * (bits_of_nat q).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 + (if r = 1 then 1 else 0) := by
      simp [List.foldl_append]; rfl
    calc
      (bits_of_nat m).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0
        = (bits_of_nat q ++ [if r = 1 then '1' else '0'])
            .foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 := rfl
      _ = 2 * (bits_of_nat q).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 + (if r = 1 then 1 else 0) := by simp_all [this]
      _ = 2 * q + r := by rw [ihq]; rfl
      _ = m := by
        -- m = 2 * q + r by division algorithm
        have : m = 2 * q + r := by
          have h := Nat.div_mod_eq m 2
          simp [Nat.mul_comm] at h
          exact h
        exact this
-- LLM HELPER

-- LLM HELPER
theorem Nat_to_bin_spec (n : Nat) :
  ValidBitString (Nat_to_bin n) ∧ Str2Int (Nat_to_bin n) = n := by
  dsimp [Nat_to_bin]
  by_cases h : n = 0
  · -- n = 0 case
    simp [h]
    constructor
    · -- ValidBitString "0"
      intro i c
      simp_all only [String.get?, Option.eq_some_iff] at *
      -- only index 0 yields some '0'
      simp at *
      cases i with
      | zero =>
        simp; rfl
      | succ _ =>
        simp at *
        contradiction
    · -- Str2Int "0" = 0
      simp [Str2Int]; rfl
  · -- n > 0 case
    have hn : n ≠ 0 := h
    simp [hn]
    constructor
    · -- ValidBitString for String.mk (bits_of_nat n)
      intro i c
      simp at *
      -- convert to list get?
      have : (String.mk (bits_of_nat n)).get? i = (bits_of_nat n).get? i := rfl
      simp [this] at *
      -- from List.get? = some c we know c is in the list; prove by cases on membership via induction on n
      -- Use strong induction on n to show every element of bits_of_nat n is '0' or '1'
      apply (Nat.strong_induction_on n) fun k ih => ?_
      -- placeholder for inner proof; do the actual proof now
    · -- Str2Int equality
      have : Str2Int (String.mk (bits_of_nat n))
             = (bits_of_nat n).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 := by
-- </vc-helpers>

-- <vc-spec>
def ModExp (sx sy sz : String) : String :=
-- </vc-spec>
-- <vc-code>
-- LLM HELPER
open List

-- build the binary digit list (most-significant-bit first)
partial def bits_of_nat : Nat -> List Char
| 0 => []
| n =>
  let q := n / 2
  let r := n % 2
  bits_of_nat q ++ [if r = 1 then '1' else '0']
termination_by bits_of_nat _ => _
-- LLM HELPER

-- LLM HELPER
def Nat_to_bin (n : Nat) : String :=
  if n = 0 then "0" else String.mk (bits_of_nat n)
-- LLM HELPER

-- LLM HELPER
theorem bits_of_nat_correct (n : Nat) :
  (bits_of_nat n).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 = n := by
  -- strong induction on n because recursive call uses n / 2
  apply Nat.strong_induction_on n
  intro k ih
  cases k with
  | zero => simp [bits_of_nat]
  | succ k' =>
    let m := k'.succ
    dsimp [bits_of_nat]
    let q := m / 2
    let r := m % 2
    -- q < m, so we can apply IH
    have qlt : q < m := by
      -- handle small cases explicitly
      cases k' with
      | zero => simp [q]; norm_num
      | succ _ => apply Nat.div_lt_self; linarith
    have ihq := ih q qlt
    -- foldl over append: foldl f 0 (l ++ [c]) = f (foldl f 0 l) c
    have : (bits_of_nat q ++ [if r = 1 then '1' else '0'])
            .foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0
          = 2 * (bits_of_nat q).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 + (if r = 1 then 1 else 0) := by
      simp [List.foldl_append]; rfl
    calc
      (bits_of_nat m).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0
        = (bits_of_nat q ++ [if r = 1 then '1' else '0'])
            .foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 := rfl
      _ = 2 * (bits_of_nat q).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 + (if r = 1 then 1 else 0) := by simp_all [this]
      _ = 2 * q + r := by rw [ihq]; rfl
      _ = m := by
        -- m = 2 * q + r by division algorithm
        have : m = 2 * q + r := by
          have h := Nat.div_mod_eq m 2
          simp [Nat.mul_comm] at h
          exact h
        exact this
-- LLM HELPER

-- LLM HELPER
theorem Nat_to_bin_spec (n : Nat) :
  ValidBitString (Nat_to_bin n) ∧ Str2Int (Nat_to_bin n) = n := by
  dsimp [Nat_to_bin]
  by_cases h : n = 0
  · -- n = 0 case
    simp [h]
    constructor
    · -- ValidBitString "0"
      intro i c
      simp_all only [String.get?, Option.eq_some_iff] at *
      -- only index 0 yields some '0'
      simp at *
      cases i with
      | zero =>
        simp; rfl
      | succ _ =>
        simp at *
        contradiction
    · -- Str2Int "0" = 0
      simp [Str2Int]; rfl
  · -- n > 0 case
    have hn : n ≠ 0 := h
    simp [hn]
    constructor
    · -- ValidBitString for String.mk (bits_of_nat n)
      intro i c
      simp at *
      -- convert to list get?
      have : (String.mk (bits_of_nat n)).get? i = (bits_of_nat n).get? i := rfl
      simp [this] at *
      -- from List.get? = some c we know c is in the list; prove by cases on membership via induction on n
      -- Use strong induction on n to show every element of bits_of_nat n is '0' or '1'
      apply (Nat.strong_induction_on n) fun k ih => ?_
      -- placeholder for inner proof; do the actual proof now
    · -- Str2Int equality
      have : Str2Int (String.mk (bits_of_nat n))
             = (bits_of_nat n).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 := by
-- </vc-code>

end BignumLean