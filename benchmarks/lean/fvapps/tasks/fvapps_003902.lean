-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_outlier (integers : List Int) : Int := sorry

theorem find_outlier_even_list (integers : List Int) 
  (h1 : integers.length ≥ 3)
  (h2 : (integers.filter (fun x => x % 2 ≠ 0)).length = 1) :
  let result := find_outlier integers
  result % 2 ≠ 0 ∧ 
  ∀ x ∈ integers, x ≠ result → x % 2 = 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_outlier_odd_list (integers : List Int)
  (h1 : integers.length ≥ 3)
  (h2 : (integers.filter (fun x => x % 2 = 0)).length = 1) :
  let result := find_outlier integers
  result % 2 = 0 ∧
  ∀ x ∈ integers, x ≠ result → x % 2 ≠ 0 := sorry
-- </vc-theorems>