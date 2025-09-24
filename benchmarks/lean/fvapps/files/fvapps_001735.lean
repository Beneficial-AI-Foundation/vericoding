-- <vc-preamble>
structure Fraction where
  num : Nat
  denom : Nat
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def gcd (a b : Nat) : Nat :=
sorry

def simplifiedFractions (n : Nat) : List String :=
sorry

def stringToFraction (s : String) : Fraction :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem fractions_are_valid {n : Nat} (h : n > 0) :
  ∀ frac, frac ∈ simplifiedFractions n →
    let f := stringToFraction frac
    0 < f.num ∧ f.num < f.denom ∧ f.denom ≤ n ∧ gcd f.num f.denom = 1 :=
sorry

theorem fractions_are_unique {n : Nat} (h : n > 0) :
  ∀ x y, x ∈ simplifiedFractions n → y ∈ simplifiedFractions n →
    x = y → stringToFraction x = stringToFraction y :=
sorry

theorem all_simplified_fractions_included {n : Nat} (h : n > 0) :
  ∀ i j : Nat, 1 ≤ i → i < j → j ≤ n → gcd i j = 1 →
    ∃ frac, frac ∈ simplifiedFractions n ∧ stringToFraction frac = ⟨i, j⟩ :=
sorry

theorem empty_for_n_less_than_2 :
  simplifiedFractions 1 = [] :=
sorry
-- </vc-theorems>