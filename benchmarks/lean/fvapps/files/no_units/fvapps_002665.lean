-- <vc-preamble>
def per (n : Nat) : List Nat := sorry

def productOfDigits (n : Nat) : Nat := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def digitsOfNat (n : Nat) : List Nat := sorry

theorem per_empty_for_single_digit (n : Nat) : 
  n < 10 → per n = [] := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem per_decreasing {n : Nat} {result : List Nat} :
  result = per n →
  ∀ i, ∀ h : i < result.length - 1,
  result.get ⟨i, sorry⟩ ≥ result.get ⟨i+1, sorry⟩ := sorry

theorem per_bounded_length (n : Nat) :
  (per n).length ≤ 100 := sorry
-- </vc-theorems>