/-
It's the fourth quater of the Super Bowl and your team is down by 4 points. You're 10 yards away from the endzone, if your team doesn't score a touchdown in the next four plays you lose. On a previous play, you were injured and rushed to the hospital. Your hospital room has no internet, tv, or radio and you don't know the results of the game. You look at your phone and see that on your way to the hospital a text message came in from one of your teamates. It contains an array of the last 4 plays in chronological order. In each play element of the array you will receive the yardage of the play and the type of the play. Have your function let you know if you won or not.

# What you know:

* Gaining greater than 10 yds from where you started is a touchdown and you win.
* Yardage of each play will always be a positive number greater than 0.
* There are only four types of plays: "run", "pass", "sack", "turnover".
* Type of plays that will gain yardage are: "run", "pass".
* Type of plays that will lose yardage are: "sack".
* Type of plays that will automatically lose the game are: "turnover".
* When a game ending play occurs the remaining (plays) arrays will be empty.
* If you win return true, if you lose return false.

# Examples:

[[8, "pass"],[5, "sack"],[3, "sack"],[5, "run"]]
`false`
[[12, "pass"],[],[],[]])
`true`
[[2, "run"],[5, "pass"],[3, "sack"],[8, "pass"]]
`true`
[[5, "pass"],[6, "turnover"],[],[]]
`false`

Good Luck!
-/

def Play := Int × PlayType
def PlayList := List Play

def turnover : PlayType := ⟨"turnover"⟩
def pass : PlayType := ⟨"pass"⟩

-- <vc-helpers>
-- </vc-helpers>

def sack : PlayType := ⟨"sack"⟩

def did_we_win (plays : PlayList) : Bool := 
  sorry

theorem did_we_win_properties (plays : PlayList) : 
  let filtered := plays.filter (fun p => true)
  let hasNoTurnovers := ¬(filtered.any (fun p => p.2 == turnover))
  let total := filtered.foldl (fun acc p => 
    acc + (if p.2 == sack then -p.1 else p.1)) 0

  did_we_win plays → (hasNoTurnovers ∧ total > 10) ∧ 
  (¬(did_we_win plays) → (¬hasNoTurnovers ∨ total ≤ 10)) :=
  sorry

theorem winning_plays (plays : PlayList) :
  plays.all (fun p => p.1 ≥ 11 && p.2 == pass) ∧ plays.length > 0 →
  did_we_win plays :=
  sorry

theorem losing_plays_yardage (plays : PlayList) :
  plays.all (fun p => p.1 ≤ 10 && p.2 == pass) ∧ plays.length > 0 →
  ¬(did_we_win plays) :=
  sorry

theorem losing_plays_turnover (plays : PlayList) :
  plays.all (fun p => p.2 == turnover) ∧ plays.length > 0 →
  ¬(did_we_win plays) :=
  sorry

/-
info: False
-/
-- #guard_msgs in
-- #eval did_we_win [[8, "pass"], [5, "sack"], [3, "sack"], [5, "run"]]

/-
info: True
-/
-- #guard_msgs in
-- #eval did_we_win [[12, "pass"], [], [], []]

/-
info: False
-/
-- #guard_msgs in
-- #eval did_we_win [[5, "pass"], [6, "turnover"], [], []]

-- Apps difficulty: introductory
-- Assurance level: unguarded