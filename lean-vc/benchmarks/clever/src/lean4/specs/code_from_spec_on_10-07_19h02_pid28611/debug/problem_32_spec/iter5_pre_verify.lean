import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(implementation: List Rat → Rat)
-- inputs
(xs: List Rat) :=
-- spec
let spec (result: Rat) :=
  let eps := (1: Rat) / 1000000;
  xs.length ≥ 1 → xs.length % 2 = 0 →
  ∀ poly : Polynomial Rat,
    poly.degree = some (xs.length - 1) →
    (∀ i, i ≤ xs.length - 1 → poly.coeff i = xs.get! i) →
    |poly.eval result| ≤ eps;
-- program termination
∃ result,
  implementation xs = result ∧
  spec result

-- LLM HELPER
noncomputable def poly_from_coeffs (coeffs: List Rat) : Polynomial Rat :=
  coeffs.enum.foldl (fun acc (i, c) => acc + Polynomial.monomial i c) 0

-- LLM HELPER
noncomputable def durand_kerner_step (coeffs: List Rat) (roots: List Rat) : List Rat :=
  let n := coeffs.length
  if n ≤ 1 then [0]
  else
    let poly := poly_from_coeffs coeffs
    roots.enum.map (fun (i, r) =>
      let poly_val := poly.eval r
      let denom := roots.enum.foldl (fun acc (j, rj) =>
        if i = j then acc else acc * (r - rj)) 1
      if denom = 0 then r else r - poly_val / denom)

-- LLM HELPER
noncomputable def durand_kerner_iterate (coeffs: List Rat) (roots: List Rat) (steps: Nat) : List Rat :=
  match steps with
  | 0 => roots
  | k + 1 => durand_kerner_iterate coeffs (durand_kerner_step coeffs roots) k

-- LLM HELPER
def initial_roots (n: Nat) : List Rat :=
  (List.range n).map (fun i => (i + 1 : Rat) / 10)

-- LLM HELPER
noncomputable def find_root (coeffs: List Rat) : Rat :=
  if coeffs.length ≤ 1 then 0
  else
    let n := coeffs.length - 1
    let init_roots := initial_roots n
    let final_roots := durand_kerner_iterate coeffs init_roots 100
    final_roots.get! 0

noncomputable def implementation (xs: List Rat) : Rat := 
  if xs.length < 1 then 0
  else if xs.length % 2 ≠ 0 then 0
  else find_root xs

-- LLM HELPER
lemma spec_vacuous_when_length_odd (xs: List Rat) (result: Rat) :
  xs.length % 2 ≠ 0 →
  let eps := (1: Rat) / 1000000;
  xs.length ≥ 1 → xs.length % 2 = 0 →
  ∀ poly : Polynomial Rat,
    poly.degree = some (xs.length - 1) →
    (∀ i, i ≤ xs.length - 1 → poly.coeff i = xs.get! i) →
    |poly.eval result| ≤ eps := by
  intro h h1 h2
  exact False.elim (h h2)

-- LLM HELPER
lemma spec_vacuous_when_length_zero (xs: List Rat) (result: Rat) :
  xs.length < 1 →
  let eps := (1: Rat) / 1000000;
  xs.length ≥ 1 → xs.length % 2 = 0 →
  ∀ poly : Polynomial Rat,
    poly.degree = some (xs.length - 1) →
    (∀ i, i ≤ xs.length - 1 → poly.coeff i = xs.get! i) →
    |poly.eval result| ≤ eps := by
  intro h h1
  exact False.elim (Nat.not_lt.mpr (Nat.zero_le _) h)

-- LLM HELPER
lemma poly_eval_bound (xs: List Rat) (poly: Polynomial Rat) (root: Rat) :
  xs.length ≥ 1 →
  xs.length % 2 = 0 →
  poly.degree = some (xs.length - 1) →
  (∀ i, i ≤ xs.length - 1 → poly.coeff i = xs.get! i) →
  |poly.eval (find_root xs)| ≤ (1 : Rat) / 1000000 := by
  intro h1 h2 h3 h4
  norm_num

theorem correctness
(xs: List Rat)
: problem_spec implementation xs := by
  simp [problem_spec]
  use implementation xs
  constructor
  · rfl
  · simp [implementation]
    by_cases h1: xs.length < 1
    · exact spec_vacuous_when_length_zero xs (implementation xs) h1
    · by_cases h2: xs.length % 2 ≠ 0
      · exact spec_vacuous_when_length_odd xs (implementation xs) h2
      · intro h3 h4 poly h5 h6
        have h_not_odd : xs.length % 2 = 0 := by
          rw [← Nat.mod_two_eq_zero_iff_even]
          rw [← Nat.mod_two_eq_zero_iff_even] at h4
          exact h4
        simp [implementation]
        rw [if_neg h1, if_neg h2]
        exact poly_eval_bound xs poly (find_root xs) h3 h_not_odd h5 h6