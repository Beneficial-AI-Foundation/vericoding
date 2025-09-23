-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_charming_boy (n : Nat) (votes : List String) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_charming_boy_in_votes (n : Nat) (votes : List String) :
  votes ≠ [] → find_charming_boy n votes ∈ votes :=
  sorry

theorem find_charming_boy_is_top_voted (n : Nat) (votes : List String) :
  votes ≠ [] →
  let result := find_charming_boy n votes 
  let count := votes.countP (· = result)
  let max_count := (votes.map (λ v => votes.countP (· = v))).maximum?.get!
  count = max_count :=
  sorry

theorem find_charming_boy_is_lex_min (n : Nat) (votes : List String) :
  votes ≠ [] →
  let result := find_charming_boy n votes
  let count := votes.countP (· = result)
  ∀ v ∈ votes, votes.countP (· = v) = count → result ≤ v :=
  sorry

theorem find_charming_boy_order_independent (n : Nat) (votes₁ votes₂ : List String) :
  votes₁.length = n →
  votes₂.length = n →
  (∀ v, votes₁.countP (· = v) = votes₂.countP (· = v)) →
  find_charming_boy n votes₁ = find_charming_boy n votes₂ :=
  sorry

theorem find_charming_boy_duplicate_invariant (n : Nat) (votes : List String) :
  votes.length = n →
  find_charming_boy n votes = find_charming_boy (2*n) (votes ++ votes) :=
  sorry

/-
info: 'john'
-/
-- #guard_msgs in
-- #eval find_charming_boy 10 "john berry berry thomas thomas john john berry thomas john".split()

/-
info: 'ramesh'
-/
-- #guard_msgs in
-- #eval find_charming_boy 4 "ramesh suresh suresh ramesh".split()

/-
info: 'andy'
-/
-- #guard_msgs in
-- #eval find_charming_boy 5 "andy bob bob andy charlie".split()
-- </vc-theorems>