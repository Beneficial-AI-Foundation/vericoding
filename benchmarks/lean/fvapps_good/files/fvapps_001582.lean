-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def mix (s1 s2 : String) : String := sorry

private def splitChar (c : Char) : Bool := c = '/'
-- </vc-definitions>

-- <vc-theorems>
theorem mix_basic_properties (s1 s2 : String) (result : String) (h : result = mix s1 s2) (h_nonempty : result ≠ "") :
  let parts := result.split splitChar
  (∀ p ∈ parts, p.startsWith "1:" ∨ p.startsWith "2:" ∨ p.startsWith "=:") ∧
  (∀ p ∈ parts, ∀ i < p.length, i ≥ 2 → p.data[i]! = p.data[2]!) ∧
  (∀ p ∈ parts, p.length > 3) := sorry

theorem mix_identical_strings (s : String) (result : String) (h : result = mix s s) (h_nonempty : result ≠ "") :
  let parts := result.split splitChar
  ∀ p ∈ parts, p.startsWith "=:" := sorry

theorem mix_no_lowercase (s : String) (h : ∀ c ∈ s.data, ¬c.isLower) :
  mix s s = "" := sorry
-- </vc-theorems>