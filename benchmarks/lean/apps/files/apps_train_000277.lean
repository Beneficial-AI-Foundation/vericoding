-- <vc-helpers>
-- </vc-helpers>

def bagOfTokensScore (tokens: List Nat) (power: Nat) : Nat :=
  sorry

theorem score_bounds {tokens: List Nat} {power: Nat} :
  let score := bagOfTokensScore tokens power
  score ≤ tokens.length ∧ score ≥ 0 :=
  sorry

theorem sorted_input_permutation {tokens s_tokens: List Nat} {power: Nat} :
  s_tokens.Perm tokens →
  bagOfTokensScore tokens power = bagOfTokensScore s_tokens power :=
  sorry

theorem empty_tokens {tokens: List Nat} {power: Nat} :
  tokens = [] → bagOfTokensScore tokens power = 0 :=
  sorry

theorem single_token {token: Nat} {power: Nat} : 
  let score := bagOfTokensScore [token] power
  score ≤ 1 ∧ score ≥ 0 ∧ score = (if token ≤ power then 1 else 0) :=
  sorry

/-
info: 0
-/
-- #guard_msgs in
-- #eval bag_of_tokens_score [100] 50

/-
info: 1
-/
-- #guard_msgs in
-- #eval bag_of_tokens_score [100, 200] 150

/-
info: 2
-/
-- #guard_msgs in
-- #eval bag_of_tokens_score [100, 200, 300, 400] 200

-- Apps difficulty: interview
-- Assurance level: unguarded