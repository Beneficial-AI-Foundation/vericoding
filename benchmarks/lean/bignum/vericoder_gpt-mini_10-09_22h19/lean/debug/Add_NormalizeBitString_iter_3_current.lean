namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

def NormalizeBitString (s : String) : String :=
  sorry

axiom NormalizeBitString_spec (s : String) (h : ValidBitString s) :
  let t := NormalizeBitString s
  ValidBitString t ∧
  t.length > 0 ∧
  (t.length > 1 → t.get? 0 = some '1') ∧
  Str2Int s = Str2Int t

-- <vc-helpers>
-- LLM HELPER
open Std

/-- Produce the list of bits of n in least-significant-first order using unfoldr. -/
def bits_rev_of_nat (n : Nat) : List Char :=
  List.unfoldr (fun m =>
    if m = 0 then none
    else
      let bit := if m % 2 = 1 then '1' else '0'
      some (bit, m / 2)
  ) n

/-- Produce a canonical bit-string for a natural number (no leading zeros, non-empty). -/
def nat_to_bits_str (n : Nat) : String :=
  if n = 0 then String.fromChars ['0']
  else String.fromChars (List.reverse (bits_rev_of_nat n))

/-- Normalization: represent any bitstring by the canonical representation of its numeric value. -/
def NormalizeBitString (s : String) : String :=
  nat_to_bits_str (Str2Int s)

-- Helper: character to numeric value
def bit_val (c : Char) : Nat := if c = '1' then 1 else 0

theorem bits_rev_of_nat_unfold (m : Nat) :
  bits_rev_of_nat m =
    match (if m = 0 then none
           else some (if m % 2 = 1 then '1' else '0', m / 2)) with
    | none => []
    | some (b, m') => b :: bits_rev_of_nat m'
    end := by
  -- By definition of List.unfoldr
  dsimp [bits_rev_of_nat, List.unfoldr]
  simp

-- Str2Int on String.fromChars reduces to fold over the given list of chars.
theorem Str2Int_fromChars (xs : List Char) :
  Str2Int (String.fromChars xs) = xs.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 := by
  dsimp [Str2Int]
  -- by definition String.fromChars xs .data = xs, so this is defeq
  rfl

-- Fold property for append: foldl over l++[c] equals (foldl over l)*2 + bit_val c
theorem foldl_append_single {α : Type} {f : α → Char → α} {init : α} (l : List Char) (c : Char)
    (h : f = fun acc ch => (2 * acc + (if ch = '1' then 1 else 0) : α)) :
    (l ++ [c]).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 =
      (l.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0) * 2 +
        (if c = '1' then 1 else 0) := by
  -- Use general foldl append lemma for numeric function
  have : (l ++ [c]).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 =
           ([c]).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) (l.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0) :=
    by
    -- List.foldl_append is available
    apply List.foldl_append
  simp [this]
  -- compute single-step fold
  dsimp
  simp

-- The main correctness lemma: converting nat to canonical bitstring and interpreting yields back the nat.
theorem Str2Int_nat_to_bits (n : Nat) : Str2Int (nat_to_bits_str n) = n := by
  dsimp [nat_to_bits_str]
  byCases h0 : n = 0
  · -- n = 0
    simp [h0, Str2Int_fromChars]
    -- String.fromChars ['0'] folds to 0
    simp [List.foldl]
  · -- n > 0: we use strong induction on n
    have hn : 0 < n := by
      have : ¬ (n = 0) := by simpa using h0
      exact Nat.pos_of_ne_zero this
    -- strong induction
    apply Nat.strongInductionOn n
    intro k ih
    dsimp [nat_to_bits_str] at *
    have hk : 0 < k := by
      have : ¬ (k = 0) := by
        -- from k≥1 since we are in nonzero case in
-- </vc-helpers>

-- <vc-spec>
def Add (s1 s2 : String) : String :=
-- </vc-spec>
-- <vc-code>
-- LLM HELPER
open Std

/-- Produce the list of bits of n in least-significant-first order using unfoldr. -/
def bits_rev_of_nat (n : Nat) : List Char :=
  List.unfoldr (fun m =>
    if m = 0 then none
    else
      let bit := if m % 2 = 1 then '1' else '0'
      some (bit, m / 2)
  ) n

/-- Produce a canonical bit-string for a natural number (no leading zeros, non-empty). -/
def nat_to_bits_str (n : Nat) : String :=
  if n = 0 then String.fromChars ['0']
  else String.fromChars (List.reverse (bits_rev_of_nat n))

/-- Normalization: represent any bitstring by the canonical representation of its numeric value. -/
def NormalizeBitString (s : String) : String :=
  nat_to_bits_str (Str2Int s)

-- Helper: character to numeric value
def bit_val (c : Char) : Nat := if c = '1' then 1 else 0

theorem bits_rev_of_nat_unfold (m : Nat) :
  bits_rev_of_nat m =
    match (if m = 0 then none
           else some (if m % 2 = 1 then '1' else '0', m / 2)) with
    | none => []
    | some (b, m') => b :: bits_rev_of_nat m'
    end := by
  -- By definition of List.unfoldr
  dsimp [bits_rev_of_nat, List.unfoldr]
  simp

-- Str2Int on String.fromChars reduces to fold over the given list of chars.
theorem Str2Int_fromChars (xs : List Char) :
  Str2Int (String.fromChars xs) = xs.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 := by
  dsimp [Str2Int]
  -- by definition String.fromChars xs .data = xs, so this is defeq
  rfl

-- Fold property for append: foldl over l++[c] equals (foldl over l)*2 + bit_val c
theorem foldl_append_single {α : Type} {f : α → Char → α} {init : α} (l : List Char) (c : Char)
    (h : f = fun acc ch => (2 * acc + (if ch = '1' then 1 else 0) : α)) :
    (l ++ [c]).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 =
      (l.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0) * 2 +
        (if c = '1' then 1 else 0) := by
  -- Use general foldl append lemma for numeric function
  have : (l ++ [c]).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 =
           ([c]).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) (l.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0) :=
    by
    -- List.foldl_append is available
    apply List.foldl_append
  simp [this]
  -- compute single-step fold
  dsimp
  simp

-- The main correctness lemma: converting nat to canonical bitstring and interpreting yields back the nat.
theorem Str2Int_nat_to_bits (n : Nat) : Str2Int (nat_to_bits_str n) = n := by
  dsimp [nat_to_bits_str]
  byCases h0 : n = 0
  · -- n = 0
    simp [h0, Str2Int_fromChars]
    -- String.fromChars ['0'] folds to 0
    simp [List.foldl]
  · -- n > 0: we use strong induction on n
    have hn : 0 < n := by
      have : ¬ (n = 0) := by simpa using h0
      exact Nat.pos_of_ne_zero this
    -- strong induction
    apply Nat.strongInductionOn n
    intro k ih
    dsimp [nat_to_bits_str] at *
    have hk : 0 < k := by
      have : ¬ (k = 0) := by
        -- from k≥1 since we are in nonzero case in
-- </vc-code>

end BignumLean