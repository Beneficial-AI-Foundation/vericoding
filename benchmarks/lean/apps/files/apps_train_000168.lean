-- <vc-preamble>
def maxProduct (nums : List Int) : Int := sorry

def listMax (xs : List Int) : Int :=
  match xs with
  | [] => 0
  | h :: t => List.foldl max h t
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def listProd (xs : List Int) : Int :=
  match xs with
  | [] => 1
  | h :: t => List.foldl (· * ·) h t
-- </vc-definitions>

-- <vc-theorems>
theorem maxProduct_empty_list :
  maxProduct [] = 0 := sorry

theorem maxProduct_single_element (x : Int) :
  maxProduct [x] = x := sorry

theorem maxProduct_nonneg_with_zero (nums : List Int) :
  (0 ∈ nums) → maxProduct nums ≥ 0 := sorry

/-
info: 6
-/
-- #guard_msgs in
-- #eval maxProduct [2, 3, -2, 4]

/-
info: 0
-/
-- #guard_msgs in
-- #eval maxProduct [-2, 0, -1]

/-
info: 24
-/
-- #guard_msgs in
-- #eval maxProduct [-2, 3, -4]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible