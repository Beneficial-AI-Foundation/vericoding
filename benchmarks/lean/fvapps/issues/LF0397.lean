-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def score_parentheses (s : ParenString) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem nested_pairs_score {n : Nat} (h : 0 < n) (h2 : n ≤ 10) :
  let s : ParenString := ⟨"(())"⟩
  score_parentheses s = 2^(n-1) :=
  sorry

theorem sequential_nested_score {depths : List Nat}
  (h1 : ∀ x ∈ depths, 0 < x ∧ x ≤ 3)
  (h2 : depths.length ≥ 1)
  (h3 : depths.length ≤ 5) :
  let s : ParenString := ⟨"(())(())"⟩
  score_parentheses s = depths.foldl (fun acc d => acc + 2^(d-1)) 0 :=
  sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval score_parentheses "()"

/-
info: 2
-/
-- #guard_msgs in
-- #eval score_parentheses "(())"

/-
info: 6
-/
-- #guard_msgs in
-- #eval score_parentheses "(()(()))"
-- </vc-theorems>