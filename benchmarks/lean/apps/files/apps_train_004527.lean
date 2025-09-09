def poly_derivative (p : List Int) : List Int :=
  sorry

def scaleList (k : Int) (xs : List Int) : List Int :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def zeroList (n : Nat) : List Int :=
  sorry

theorem derivative_length {p : List Int} (h : p ≠ []) :
  (poly_derivative p).length = p.length - 1 :=
sorry

theorem derivative_constant {p : List Int} (h : p.length = 1) :
  poly_derivative p = [] :=
sorry

theorem derivative_linear {p : List Int} (h : p.length ≥ 2) :
  (poly_derivative p).get! 0 = p.get! 1 :=
sorry

/-
info: [2]
-/
-- #guard_msgs in
-- #eval poly_derivative [1, 2]

/-
info: [1, 6]
-/
-- #guard_msgs in
-- #eval poly_derivative [9, 1, 3]

/-
info: [2, 6, 12]
-/
-- #guard_msgs in
-- #eval poly_derivative [1, 2, 3, 4]

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible