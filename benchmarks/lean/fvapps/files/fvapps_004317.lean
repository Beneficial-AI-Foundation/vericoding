-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def play_if_enough (hand play : String) : Bool × String :=
  sorry

def String.count (s : String) (c : Char) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem play_if_enough_success_length {hand play : String} :
  let res := play_if_enough hand play
  res.1 → res.2.length = hand.length - play.length :=
sorry

theorem play_if_enough_success_subset {hand play : String} {c : Char} :
  let res := play_if_enough hand play
  res.1 → res.2.count c ≤ hand.count c :=
sorry

theorem play_if_enough_failure_preserves {hand play : String} :
  let res := play_if_enough hand play
  ¬res.1 → res.2 = hand :=
sorry

theorem play_if_enough_empty_succeeds {hand : String} :
  (play_if_enough hand "").1 = true :=
sorry

theorem play_if_enough_too_long_fails {hand play : String} :
  play.length > hand.length →
  ¬(play_if_enough hand play).1 :=
sorry

theorem play_if_enough_impossible_preserves {hand : String} :
  let impossible := String.mk (List.replicate (hand.length + 1) 'z')
  let res := play_if_enough hand impossible
  ¬res.1 ∧ res.2 = hand :=
sorry
-- </vc-theorems>