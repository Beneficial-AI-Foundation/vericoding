-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def buy_newspaper (s1 : String) (s2 : String) : Int := sorry

theorem buy_newspaper_invalid_chars
  (s1 : String)
  (s2 : String)
  (h : ∃ c, c ∈ s2.data ∧ c ∉ s1.data) :
  buy_newspaper s1 s2 = -1 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem buy_newspaper_valid_chars
  (s1 : String)
  (s2 : String)
  (h1 : s2.length > 0)
  (h2 : ∀ c, c ∈ s2.data → c ∈ s1.data) :
  buy_newspaper s1 s2 ≥ 0 := sorry
-- </vc-theorems>