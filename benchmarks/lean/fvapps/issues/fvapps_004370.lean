-- <vc-preamble>
def contestant_score (c : Contestant) : Nat :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def scoreboard (contestants : List Contestant) : List Contestant :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem scoreboard_preserves_length (contestants : List Contestant) :
  List.length (scoreboard contestants) = List.length contestants :=
  sorry

theorem scoreboard_sorted_scores (contestants : List Contestant) 
    (h : contestants.length > 1) :
  let result := scoreboard contestants
  ∀ i : Fin (result.length),
    i.val + 1 < result.length →
    let score₁ := contestant_score (result.get i)
    let score₂ := contestant_score (result.get ⟨i.val + 1, by sorry⟩)
    if score₁ = score₂ 
    then (result.get i).name ≤ (result.get ⟨i.val + 1, by sorry⟩).name 
    else score₁ > score₂ :=
  sorry

theorem empty_scoreboard :
  scoreboard [] = [] :=
  sorry

/-
info: expected1
-/
-- #guard_msgs in
-- #eval scoreboard [{"name": "Billy The Beast", "chickenwings": 17, "hamburgers": 7, "hotdogs": 8}, {"name": "Habanero Hillary", "chickenwings": 5, "hamburgers": 17, "hotdogs": 11}, {"name": "Joey Jaws", "chickenwings": 8, "hamburgers": 8, "hotdogs": 15}, {"name": "Big Bob", "chickenwings": 20, "hamburgers": 4, "hotdogs": 11}]

/-
info: expected2
-/
-- #guard_msgs in
-- #eval scoreboard [{"name": "Joey Jaws", "chickenwings": 0, "hamburgers": 1, "hotdogs": 1}, {"name": "Big Bob", "chickenwings": 1, "hamburgers": 0, "hotdogs": 0}]

/-
info: []
-/
-- #guard_msgs in
-- #eval scoreboard []
-- </vc-theorems>