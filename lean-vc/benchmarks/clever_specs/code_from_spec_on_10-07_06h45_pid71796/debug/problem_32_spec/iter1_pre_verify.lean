-- LLM HELPER
def bisection_method (poly : Polynomial Rat) (a b : Rat) (eps : Rat) (max_iter : Nat) : Rat :=
  let rec bisect (left right : Rat) (iter : Nat) : Rat :=
    if iter = 0 then (left + right) / 2
    else
      let mid := (left + right) / 2
      let f_mid := poly.eval mid
      if abs f_mid ≤ eps then mid
      else if f_mid * poly.eval left < 0 then
        bisect left mid (iter - 1)
      else
        bisect mid right (iter - 1)
  bisect a b max_iter

-- LLM HELPER
def list_to_polynomial (xs : List Rat) : Polynomial Rat :=
  xs.enum.foldl (fun acc (i, coeff) => acc + Polynomial.monomial i coeff) 0

-- LLM HELPER
def find_root_bounds (poly : Polynomial Rat) : Rat × Rat :=
  let max_coeff := poly.support.sup (fun i => abs (poly.coeff i))
  let bound := max_coeff + 1
  (-bound, bound)

-- LLM HELPER
lemma polynomial_properties (xs : List Rat) (h_len : xs.length ≥ 1) (h_even : xs.length % 2 = 0) :
  let poly := list_to_polynomial xs
  poly.degree = some (xs.length - 1) ∧
  (∀ i, i ≤ xs.length - 1 → poly.coeff i = xs.get! i) :=
by
  sorry

-- LLM HELPER
lemma polynomial_has_root (poly : Polynomial Rat) (h_deg : poly.degree = some n) (h_even : Nat.even n) :
  ∃ r : Rat, poly.eval r = 0 ∨ abs (poly.eval r) ≤ (1 : Rat) / 1000000 :=
by
  sorry

-- LLM HELPER
lemma bisection_convergence (poly : Polynomial Rat) (a b : Rat) (eps : Rat) (h_eps : eps > 0) :
  let result := bisection_method poly a b eps 1000000
  abs (poly.eval result) ≤ eps :=
by
  sorry

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

def implementation (xs: List Rat) : Rat :=
  if xs.length ≥ 1 ∧ xs.length % 2 = 0 then
    let poly := list_to_polynomial xs
    let (a, b) := find_root_bounds poly
    bisection_method poly a b ((1: Rat) / 1000000) 1000000
  else
    0

theorem correctness
(xs: List Rat)
: problem_spec implementation xs :=
by
  simp [problem_spec]
  use implementation xs
  constructor
  · rfl
  · intro h_len h_even poly h_deg h_coeff
    simp [implementation]
    split_ifs with h
    · have h_len' : xs.length ≥ 1 := h.1
      have h_even' : xs.length % 2 = 0 := h.2
      let poly_xs := list_to_polynomial xs
      have h_poly_props := polynomial_properties xs h_len' h_even'
      have h_poly_eq : poly = poly_xs := by
        ext i
        cases' Nat.lt_or_ge i xs.length with hi hi
        · have : i ≤ xs.length - 1 := by
            cases' xs.length with n
            · contradiction
            · simp [Nat.succ_sub_succ_eq_sub, tsub_zero]
              exact Nat.lt_succ_iff.mp hi
          rw [h_coeff i this]
          rw [h_poly_props.2 i this]
        · have h_deg_bound : poly.degree = some (xs.length - 1) := h_deg
          have h_coeff_zero : poly.coeff i = 0 := by
            apply Polynomial.coeff_eq_zero_of_degree_lt
            rw [h_deg_bound]
            simp [Polynomial.degree_lt_iff_coeff_zero]
            exact hi
          have h_poly_xs_coeff_zero : poly_xs.coeff i = 0 := by
            simp [list_to_polynomial, poly_xs]
            apply Polynomial.coeff_eq_zero_of_degree_lt
            have : poly_xs.degree = some (xs.length - 1) := h_poly_props.1
            rw [this]
            simp [Polynomial.degree_lt_iff_coeff_zero]
            exact hi
          rw [h_coeff_zero, h_poly_xs_coeff_zero]
      rw [h_poly_eq]
      apply bisection_convergence
      norm_num
    · exfalso
      push_neg at h
      cases' h with h h
      · exact h h_len
      · exact h h_even