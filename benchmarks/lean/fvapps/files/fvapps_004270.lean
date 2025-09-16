-- <vc-preamble>
def share_price (invested : Float) (changes : List Float) : String :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def parseFloat? (s : String) : Option Float :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem share_price_valid_format {invested : Float} {changes : List Float}
  (h1 : invested > 0)
  (h2 : ∀ c ∈ changes, c ≥ -99.99 ∧ c ≤ 1000) :
  ∃ p d, 
    share_price invested changes = p ++ "." ++ d ∧  
    d.length = 2 ∧
    (parseFloat? (share_price invested changes)).isSome ∧ 
    ∃ x, parseFloat? (share_price invested changes) = some x ∧ x ≥ 0 := sorry

theorem share_price_empty_changes {invested : Float}
  (h : invested > 0) :
  share_price invested [] = toString invested ++ "." ++ "00" := sorry

/-
info: '100.00'
-/
-- #guard_msgs in
-- #eval share_price 100 []

/-
info: '75.00'
-/
-- #guard_msgs in
-- #eval share_price 100 [-50, 50]

/-
info: '1113.64'
-/
-- #guard_msgs in
-- #eval share_price 1000 [0, 2, 3, 6]
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded