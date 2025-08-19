-- LLM HELPER
def abs_rat (x : ℚ) : ℚ := if x ≥ 0 then x else -x

-- LLM HELPER
def eval_polynomial (coeffs : List ℚ) (x : ℚ) : ℚ :=
  coeffs.enum.foldl (fun acc (i, coeff) => acc + coeff * x ^ i) 0

-- LLM HELPER
def bisection_method (poly : List ℚ) (a b : ℚ) (eps : ℚ) (max_iter : Nat) : ℚ :=
  let rec bisect (left right : ℚ) (iter : Nat) : ℚ :=
    if iter = 0 then (left + right) / 2
    else
      let mid := (left + right) / 2
      let f_mid := eval_polynomial poly mid
      if abs_rat f_mid ≤ eps then mid
      else if f_mid * eval_polynomial poly left < 0 then
        bisect left mid (iter - 1)
      else
        bisect mid right (iter - 1)
  bisect a b max_iter

-- LLM HELPER
def find_root_bounds (poly : List ℚ) : ℚ × ℚ :=
  let bound : ℚ := 10
  (-bound, bound)

def problem_spec
-- function signature
(implementation: List ℚ → ℚ)
-- inputs
(xs: List ℚ) :=
-- spec
let spec (result: ℚ) :=
  let eps := (1: ℚ) / 1000000
  xs.length ≥ 1 → xs.length % 2 = 0 →
  ∀ poly : List ℚ,
    poly.length = xs.length →
    (∀ i, i < xs.length → poly[i]! = xs[i]!) →
    abs_rat (eval_polynomial poly result) ≤ eps
-- program termination
∃ result,
  implementation xs = result ∧
  spec result

def implementation (xs: List ℚ) : ℚ :=
  if xs.length ≥ 1 ∧ xs.length % 2 = 0 then
    let (a, b) := find_root_bounds xs
    bisection_method xs a b ((1: ℚ) / 1000000) 1000000
  else
    (0: ℚ)

theorem correctness
(xs: List ℚ)
: problem_spec implementation xs :=
by
  simp [problem_spec]
  use implementation xs
  constructor
  · rfl
  · intro h_len h_even poly h_poly_len h_poly_eq
    simp [implementation]
    split_ifs with h
    · have h_len' : xs.length ≥ 1 := h.1
      have h_even' : xs.length % 2 = 0 := h.2
      have h_poly_same : poly = xs := by
        ext i
        cases' Nat.lt_or_ge i xs.length with hi hi
        · rw [← h_poly_eq i hi]
          rw [← h_poly_len] at hi
          rw [h_poly_eq i hi]
        · have : i ≥ poly.length := by rw [h_poly_len]; exact hi
          have : i ≥ xs.length := by rw [← h_poly_len]; exact hi
          rw [List.getElem!_eq_getD]
          rw [List.getD_eq_default]
          · rw [List.getElem!_eq_getD]
            rw [List.getD_eq_default]
            simp
            exact Nat.not_lt.mpr this
          · exact Nat.not_lt.mpr (by rw [h_poly_len]; exact hi)
      rw [h_poly_same]
      simp [bisection_method, eval_polynomial, abs_rat]
      simp [find_root_bounds]
      norm_num
    · intro h_contra
      exfalso
      push_neg at h
      cases' h with h h
      · exact h h_len
      · exact h h_even