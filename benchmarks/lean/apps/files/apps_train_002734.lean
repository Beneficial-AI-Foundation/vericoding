-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def coin (n : Nat) : List String := sorry

theorem coin_length (n : Nat) : 
  n ≤ 10 → List.length (coin n) = 2^n := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem coin_elem_length (n : Nat) (s : String) :
  n ≤ 10 → s ∈ coin n → String.length s = n := sorry

theorem coin_valid_chars (n : Nat) (s : String) (c : Char) :
  n ≤ 10 → s ∈ coin n → c ∈ s.data → c = 'H' ∨ c = 'T' := sorry

theorem coin_sorted (n : Nat) (i j : Nat) :
  n ≤ 10 → i < j → j < List.length (coin n) → 
  (coin n).get ⟨i, by sorry⟩ ≤ (coin n).get ⟨j, by sorry⟩ := sorry

theorem coin_unique (n : Nat) :
  n ≤ 10 → List.Nodup (coin n) := sorry

theorem coin_empty :
  coin 0 = [""] := sorry

theorem coin_negative (n : Int) :
  n < 0 → coin (Int.toNat n) = [] := sorry

/-
info: ['H', 'T']
-/
-- #guard_msgs in
-- #eval coin 1

/-
info: ['HH', 'HT', 'TH', 'TT']
-/
-- #guard_msgs in
-- #eval coin 2

/-
info: ['HHH', 'HHT', 'HTH', 'HTT', 'THH', 'THT', 'TTH', 'TTT']
-/
-- #guard_msgs in
-- #eval coin 3
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded