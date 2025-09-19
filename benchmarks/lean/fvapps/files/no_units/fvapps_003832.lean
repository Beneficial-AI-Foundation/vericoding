-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def transform (num : Nat) (base : Nat) : List (Nat ⊕ String) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem transform_valid_digits {n : Nat} {b : Nat} (h1 : n ≥ 1) (h2 : 2 ≤ b) (h3 : b ≤ 12) :
  let result := transform n b
  ∀ x ∈ result, 
    (∃ d : Nat, x = Sum.inl d ∧ d < 10) ∨ 
    (∃ s : String, x = Sum.inr s ∧ s = "x") :=
  sorry

theorem transform_digit_range {n : Nat} {b : Nat} (h1 : n ≥ 1) (h2 : 2 ≤ b) (h3 : b ≤ 12) :
  let result := transform n b
  ∀ x ∈ result, 
    match x with
    | Sum.inl d => d < 10
    | Sum.inr s => s = "x"
  :=
  sorry
-- </vc-theorems>