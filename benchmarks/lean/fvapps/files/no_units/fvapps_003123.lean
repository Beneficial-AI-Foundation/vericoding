-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def trump_detector (s : String) : Float := sorry

theorem trump_detector_returns_float (text : String) : 
  let result := trump_detector text
  result ≥ 0 ∨ result < 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem trump_detector_all_vowels (text : String) :
  (∀ c ∈ text.data, c ∈ ['a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U']) →
  trump_detector text ≥ 0 := sorry

theorem trump_detector_no_vowels (text : String) :
  (∀ c ∈ text.data, c ∉ ['a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U']) →
  text.length > 0 →
  trump_detector text = 0 := sorry

theorem trump_detector_rounding (text : String) :
  let result := trump_detector text
  Float.abs (result - result) < 1e-10 := sorry

theorem trump_detector_empty :
  trump_detector "" = 0 := sorry
-- </vc-theorems>