import Mathlib
-- <vc-preamble>
def Abs (x : Int) : Int :=
  if x ≥ 0 then x else -x

def AliceWins (X Y : Int) : Prop :=
  Abs (X - Y) > 1

def BrownWins (X Y : Int) : Prop :=
  Abs (X - Y) ≤ 1

def ValidInput (X Y : Int) : Prop :=
  X ≥ 0 ∧ Y ≥ 0

@[reducible, simp]
def solve_precond (X Y : Int) : Prop :=
  ValidInput X Y
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: Lemmas for the proof
lemma alice_wins_iff (X Y : Int) : AliceWins X Y ↔ Abs (X - Y) > 1 := by rfl

lemma brown_wins_iff (X Y : Int) : BrownWins X Y ↔ Abs (X - Y) ≤ 1 := by rfl

lemma alice_or_brown_wins (X Y : Int) : AliceWins X Y ∨ BrownWins X Y := by
  unfold AliceWins BrownWins
  exact Int.lt_or_le 1 (Abs (X - Y))

lemma not_both_win (X Y : Int) : ¬(AliceWins X Y ∧ BrownWins X Y) := by
  unfold AliceWins BrownWins
  intro h
  exact Int.not_le_of_gt h.1 h.2
-- </vc-helpers>

-- <vc-definitions>
def solve (X Y : Int) (h_precond : solve_precond X Y) : String :=
  if Abs (X - Y) > 1 then "Alice" else "Brown"
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (X Y : Int) (winner : String) (h_precond : solve_precond X Y) : Prop :=
  (winner = "Alice" ∨ winner = "Brown") ∧
  (winner = "Alice" ↔ AliceWins X Y) ∧
  (winner = "Brown" ↔ BrownWins X Y)

theorem solve_spec_satisfied (X Y : Int) (h_precond : solve_precond X Y) :
    solve_postcond X Y (solve X Y h_precond) h_precond := by
  unfold solve solve_postcond
  simp only [alice_wins_iff, brown_wins_iff]
  split_ifs with h
  · simp [h]
  · simp [Int.le_of_not_gt h]
-- </vc-theorems>
