-- <vc-preamble>
def abs (n : Nat) : Nat :=
  if n ≥ 0 then n else 0
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def list_prod (l : List Nat) : Nat := sorry

def find_difference (a b : List Nat) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_difference_non_negative (a b : List Nat) (h₁ : a ≠ []) (h₂ : b ≠ []) :
  find_difference a b ≥ 0 :=
sorry

theorem find_difference_symmetry (a b : List Nat) (h₁ : a ≠ []) (h₂ : b ≠ []) :
  find_difference a b = find_difference b a :=
sorry

theorem find_difference_identity (a : List Nat) (h : a ≠ []) :
  find_difference a a = 0 :=
sorry
-- </vc-theorems>