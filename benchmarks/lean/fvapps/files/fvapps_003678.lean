-- <vc-preamble>
def count_zeros (l : List Int) : Nat :=
  l.filter (· = 0) |>.length
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def product_sans_n (nums : List Int) : List Int := sorry

def List.product (l : List Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem product_sans_n_length {nums : List Int} (h : nums ≠ []) :
  (product_sans_n nums).length = nums.length :=
sorry
-- </vc-theorems>