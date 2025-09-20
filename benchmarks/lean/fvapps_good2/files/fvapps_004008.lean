-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def complex_sum (arr : List String) : String :=
sorry

def complex_str (real imag : Int) : String :=
sorry

def real_part (s : String) : Int :=
sorry

def imag_part (s : String) : Int :=
sorry

def list_sum (l : List Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem complex_sum_equals_separate_sums {arr : List String} :
  ∀ (real_sum imag_sum : Int),
  complex_sum arr = complex_str real_sum imag_sum →
  real_sum = list_sum (arr.map real_part) ∧
  imag_sum = list_sum (arr.map imag_part) :=
sorry

theorem pure_imaginary_sum {arr : List String} :
  arr.all (λ s => s = "i") →
  complex_sum arr = complex_str 0 arr.length :=
sorry

theorem empty_list_sums_to_zero :
  complex_sum [] = "0" :=
sorry

theorem zeros_sum_to_zero {arr : List String} :
  arr.all (λ s => s = "0") →
  complex_sum arr = "0" :=
sorry
-- </vc-theorems>