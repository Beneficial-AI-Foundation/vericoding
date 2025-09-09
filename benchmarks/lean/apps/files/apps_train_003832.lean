-- <vc-helpers>
-- </vc-helpers>

def transform (num : Nat) (base : Nat) : List (Nat ⊕ String) :=
  sorry

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

-- Apps difficulty: introductory
-- Assurance level: guarded