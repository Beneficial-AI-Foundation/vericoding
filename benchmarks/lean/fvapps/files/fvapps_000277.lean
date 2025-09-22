-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def bagOfTokensScore (tokens: List Nat) (power: Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
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
-- </vc-theorems>