/- 
function_signature: "def find_zero(xs: list)"
docstring: |
    xs are coefficients of a polynomial.
    find_zero find x such that poly(x) = 0.
    find_zero returns only only zero point, even if there are many.
    Moreover, find_zero only takes list xs having even number of coefficients
    and largest non zero coefficient as it guarantees a solution.
    Note(George): This problem has been modified from the original HumanEval spec because of Real is not a computable type, but a zero does not necessarily exist over the rationals.
test_cases:
  - input: [1, 2]
    output: -0.5
  - input: [-6, 11, -6, 1]
    output: 1.0
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

-- LLM HELPER
def eval_poly (xs: List Rat) (x: Rat) : Rat :=
  xs.mapIdx (fun i coeff => coeff * x^i) |>.sum

-- LLM HELPER
def eval_poly_deriv (xs: List Rat) (x: Rat) : Rat :=
  xs.mapIdx (fun i coeff => if i = 0 then 0 else coeff * (i : Rat) * x^(i - 1)) |>.sum

-- LLM HELPER
def newton_step (xs: List Rat) (x: Rat) : Rat :=
  let f := eval_poly xs x
  let df := eval_poly_deriv xs x
  if df = 0 then x else x - f / df

-- LLM HELPER
def newton_iterate (xs: List Rat) (x: Rat) : Nat → Rat
  | 0 => x
  | n + 1 => newton_step xs (newton_iterate xs x n)

def implementation (xs: List Rat) : Rat :=
  if xs.length = 2 then
    -xs[0]! / xs[1]!
  else
    newton_iterate xs 0 50

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
    (∀ i, i ≤ xs.length - 1 → poly.coeff i = xs[i]!) →
    |poly.eval result| ≤ eps;
-- program termination
∃ result,
  implementation xs = result ∧
  spec result

-- LLM HELPER
lemma linear_case (a b : Rat) (hb : b ≠ 0) :
  let poly : Polynomial Rat := Polynomial.C a + Polynomial.C b * Polynomial.X
  poly.eval (-a / b) = 0 := by
  simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  field_simp
  ring

-- LLM HELPER
lemma eval_poly_eq_polynomial_eval (xs: List Rat) (x: Rat) :
  xs.length ≥ 1 →
  ∃ poly : Polynomial Rat,
    poly.degree = some (xs.length - 1) ∧
    (∀ i, i ≤ xs.length - 1 → poly.coeff i = xs[i]!) ∧
    eval_poly xs x = poly.eval x := by
  intro h
  let poly := Polynomial.ofFinset (Finset.range xs.length) (fun i => xs[i]!)
  use poly
  constructor
  · have : xs.length > 0 := Nat.pos_of_ne_zero (Nat.one_le_iff_ne_zero.mp h)
    simp [Polynomial.degree_ofFinset_le]
    sorry
  constructor
  · intro i hi
    simp [Polynomial.coeff_ofFinset]
    by_cases h_in : i < xs.length
    · simp [h_in]
    · simp [h_in]
      have : i ≥ xs.length := Nat.le_of_not_gt h_in
      have : i > xs.length - 1 := by omega
      contradiction
  · simp [eval_poly, Polynomial.eval_ofFinset]

theorem correctness
(xs: List Rat)
: problem_spec implementation xs
:= by
  unfold problem_spec
  use implementation xs
  constructor
  · rfl
  · intro spec h_len h_even poly h_degree h_coeff
    unfold implementation
    split_ifs with h
    · -- Linear case: xs.length = 2
      have h_len_eq : xs.length = 2 := h
      have h_nonzero : xs[1]! ≠ 0 := by
        by_contra h_zero
        have : poly.degree = some 1 := by rw [h_degree, h_len_eq]; norm_num
        have : poly.coeff 1 = 0 := by rw [h_zero, ← h_coeff]; norm_num
        have : poly.degree ≤ some 0 := by
          rw [Polynomial.degree_le_iff_coeff_zero]
          intro n hn
          simp at hn
          cases' hn with hn hn
          · exact this
          · have : n ≥ 2 := Nat.succ_succ_ne_one n ▸ hn
            exact h_coeff n (by omega)
        rw [this] at *
        norm_num at *
      have : |poly.eval (-xs[0]! / xs[1]!)| = 0 := by
        have h_poly_form : poly = Polynomial.C xs[0]! + Polynomial.C xs[1]! * Polynomial.X := by
          ext n
          cases n with
          | zero => simp [h_coeff 0 (by omega)]
          | succ m =>
            cases m with
            | zero => simp [h_coeff 1 (by omega)]
            | succ k => 
              simp
              have : k + 2 > 1 := by omega
              have : k + 2 ≤ xs.length - 1 := by omega
              exact h_coeff (k + 2) this
        rw [h_poly_form]
        rw [linear_case xs[0]! xs[1]! h_nonzero]
        simp
      simp at this
      exact le_of_eq this
    · -- General case: Newton's method approximation
      sorry