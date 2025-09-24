-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def calc_weighted_sum (arr : List Int) : Int := sorry

def list_sum (xs : List Int) : Int :=
  match xs with
  | [] => 0
  | h :: t => h + list_sum t
-- </vc-definitions>

-- <vc-theorems>
theorem weighted_sum_bounds (arr : List Int) : 
  let result := calc_weighted_sum arr
  result ≥ 0 ∧ result ≤ arr.length * 6 := sorry

theorem weighted_sum_multiples_six {arr : List Int} (h : arr.length > 0) :
  let multiples := arr.map (· * 6)
  calc_weighted_sum multiples = 6 * multiples.length := sorry

theorem weighted_sum_modulo (arr : List Int) :
  calc_weighted_sum arr = arr.foldr (λ x sum => 
    if x % 6 = 0 then sum + 6 
    else sum + x % 6) 0 := sorry
-- </vc-theorems>