-- <vc-preamble>
def listMax (xs : List Int) : Int :=
  match xs with
  | [] => 0
  | h :: t => List.foldl max h t

def listProd (xs : List Int) : Int :=
  match xs with
  | [] => 1
  | h :: t => List.foldl (· * ·) h t
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def maxProduct (nums : List Int) : Int := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem maxProduct_empty_list :
  maxProduct [] = 0 :=
sorry

theorem maxProduct_single_element (x : Int) :
  maxProduct [x] = x :=
sorry

theorem maxProduct_nonneg_with_zero (nums : List Int) :
  (0 ∈ nums) → maxProduct nums ≥ 0 :=
sorry
-- </vc-theorems>