-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def calculate_cthulhu_code (i k s a_i b_i : Int) : Float := sorry

theorem cthulhu_code_finite (i k s a_i b_i : Int) 
  (h1 : i ≥ 1) (h2 : k ≥ 1) (h3 : s ≥ 1) 
  (h4 : -1000 ≤ a_i) (h5 : a_i ≤ 1000)
  (h6 : -1000 ≤ b_i) (h7 : b_i ≤ 1000) :
  let result := calculate_cthulhu_code i k s a_i b_i
  Float.isFinite result := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem cthulhu_code_formula (i k s a_i b_i : Int)
  (h1 : i ≥ 1) (h2 : k ≥ 1) (h3 : s ≥ 1)
  (h4 : -1000 ≤ a_i) (h5 : a_i ≤ 1000) 
  (h6 : -1000 ≤ b_i) (h7 : b_i ≤ 1000) :
  let result := calculate_cthulhu_code i k s a_i b_i
  let expected := (Float.ofInt (a_i + b_i)) / (Float.ofInt (2^s.toNat))
  Float.abs (result - expected) < 0.01 := sorry

theorem cthulhu_code_symmetric (i k s a_i b_i : Int)
  (h1 : i ≥ 1) (h2 : k ≥ 1) (h3 : s ≥ 1)
  (h4 : -1000 ≤ a_i) (h5 : a_i ≤ 1000)
  (h6 : -1000 ≤ b_i) (h7 : b_i ≤ 1000) :
  let result1 := calculate_cthulhu_code i k s a_i b_i
  let result2 := calculate_cthulhu_code i k s b_i a_i 
  Float.abs (result1 - result2) < 0.01 := sorry
-- </vc-theorems>