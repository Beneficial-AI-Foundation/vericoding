def complex_sum (arr : List String) : String := sorry

def complex_str (real imag : Int) : String := sorry

def real_part (s : String) : Int := sorry
def imag_part (s : String) : Int := sorry

-- <vc-helpers>
-- </vc-helpers>

def list_sum (l : List Int) : Int := sorry

-- Sum of complex numbers is equal to sum of separate numbers

theorem complex_sum_equals_separate_sums {arr : List String} : 
  ∀ (real_sum imag_sum : Int), 
  complex_sum arr = complex_str real_sum imag_sum →
  real_sum = list_sum (arr.map real_part) ∧ 
  imag_sum = list_sum (arr.map imag_part) := sorry

-- Sum of pure imaginary numbers has no real part

theorem pure_imaginary_sum {arr : List String} :
  arr.all (λ s => s = "i") →
  complex_sum arr = complex_str 0 arr.length := sorry

-- Empty list sums to zero

theorem empty_list_sums_to_zero :
  complex_sum [] = "0" := sorry

-- List of zeros sums to zero 

theorem zeros_sum_to_zero {arr : List String} :
  arr.all (λ s => s = "0") →
  complex_sum arr = "0" := sorry

/-
info: '5+2i'
-/
-- #guard_msgs in
-- #eval complex_sum ["2+3i", "3-i"]

/-
info: '6i'
-/
-- #guard_msgs in
-- #eval complex_sum ["i", "2i", "3i"]

/-
info: '0'
-/
-- #guard_msgs in
-- #eval complex_sum []

-- Apps difficulty: introductory
-- Assurance level: unguarded