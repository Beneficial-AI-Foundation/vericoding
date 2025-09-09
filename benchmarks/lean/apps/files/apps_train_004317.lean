def play_if_enough (hand play : String) : Bool × String :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def String.count (s : String) (c : Char) : Nat :=
  sorry

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

/-
info: (False, '')
-/
-- #guard_msgs in
-- #eval play_if_enough "" "bw"

/-
info: (True, 'oogssbbb')
-/
-- #guard_msgs in
-- #eval play_if_enough "ooooogggssbbb" "ooogg"

/-
info: (False, 'oogssbbb')
-/
-- #guard_msgs in
-- #eval play_if_enough "oogssbbb" "bwsg"

-- Apps difficulty: introductory
-- Assurance level: unguarded