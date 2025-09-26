import Mathlib
-- <vc-preamble>
def IntToString (n : Int) : String :=
  sorry

def ReverseString (s : String) : String :=
  sorry

def StringToInt (s : String) : Int :=
  sorry

def SumOfPalindromes (k : Int) : Int :=
  sorry

def ValidInput (k p : Int) : Prop :=
  k ≥ 1 ∧ p ≥ 1

@[reducible, simp]
def solve_precond (k p : Int) : Prop :=
  ValidInput k p
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
/--
`mod_bounds` proves that for a positive modulus `p`, the result of `%` is always
in the range `[0, p-1]`.
-/
theorem mod_bounds (a p : Int) (hp : p ≥ 1) : 0 ≤ a % p ∧ a % p < p := by
  have p_pos : 0 < p := by linarith [hp]
  exact ⟨Int.emod_nonneg a (ne_of_gt p_pos), Int.emod_lt_of_pos a p_pos⟩
-- </vc-helpers>

-- <vc-definitions>
def solve (k p : Int) (h_precond : solve_precond k p) : Int :=
  (SumOfPalindromes k) % p
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (k p : Int) (result : Int) (h_precond : solve_precond k p) : Prop :=
  0 ≤ result ∧ result < p ∧ result = (SumOfPalindromes k) % p

theorem solve_spec_satisfied (k p : Int) (h_precond : solve_precond k p) :
    solve_postcond k p (solve k p h_precond) h_precond := by
  {
  simp [solve, solve_postcond]
  rcases h_precond with ⟨_, hp⟩
  exact mod_bounds (SumOfPalindromes k) p hp
}
-- </vc-theorems>
