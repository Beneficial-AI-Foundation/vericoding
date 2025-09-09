-- <vc-helpers>
-- </vc-helpers>

def rank_teams (votes : List String) : String := sorry

theorem rank_teams_output_length {votes : List String} 
  (h1 : ∀ v ∈ votes, v.length = votes[0]!.length)
  (h2 : ∀ v ∈ votes, v.toList.Nodup) :
  (rank_teams votes).length = votes[0]!.length :=
sorry

theorem rank_teams_content {votes : List String}
  (h1 : ∀ v ∈ votes, v.length = votes[0]!.length) 
  (h2 : ∀ v ∈ votes, v.toList.Nodup) :
  ∀ c ∈ (rank_teams votes).data, c.isUpper :=
sorry

theorem rank_teams_same_chars {votes : List String}
  (h1 : ∀ v ∈ votes, v.length = votes[0]!.length)
  (h2 : ∀ v ∈ votes, v.toList.Nodup) :
  (rank_teams votes).data = votes[0]!.data :=
sorry

theorem rank_teams_single_team {votes : List String}
  (h : ∀ v ∈ votes, v = "A") :
  rank_teams votes = "A" :=
sorry

/-
info: 'ACB'
-/
-- #guard_msgs in
-- #eval rank_teams ["ABC", "ACB", "ABC", "ACB", "ACB"]

/-
info: 'XWYZ'
-/
-- #guard_msgs in
-- #eval rank_teams ["WXYZ", "XYZW"]

/-
info: 'ZMNAGUEDSJYLBOPHRQICWFXTVK'
-/
-- #guard_msgs in
-- #eval rank_teams ["ZMNAGUEDSJYLBOPHRQICWFXTVK"]

-- Apps difficulty: interview
-- Assurance level: unguarded