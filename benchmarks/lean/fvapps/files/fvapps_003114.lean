-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def clonewars (n : Int) : List Int := sorry

theorem clonewars_positive (n : Int) (h : 0 ≤ n ∧ n ≤ 10) :
  let result := clonewars n
  List.length result = 2 ∧
  1 ≤ List.get! result 0 ∧ 
  0 ≤ List.get! result 1 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem clonewars_negative (n : Int) (h : n < 0) :
  clonewars n = [1, 0] := sorry

theorem clonewars_growth (n : Int) (h : 1 ≤ n ∧ n ≤ 10) :
  let smaller := clonewars (n-1)
  let bigger := clonewars n
  List.get! bigger 0 ≥ List.get! smaller 0 ∧
  List.get! bigger 1 ≥ List.get! smaller 1 := sorry

theorem clonewars_base_cases :
  clonewars 0 = [1, 0] ∧
  clonewars 1 = [1, 1] := sorry
-- </vc-theorems>