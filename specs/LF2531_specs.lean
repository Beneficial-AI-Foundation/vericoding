-- <vc-preamble>
def GameResults := List (RoundData × Bool)

def shoot : GameResults → String := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def calculateScore (shots : String) (double : Bool) : Nat :=
  (shots.foldl (fun acc c => if c = 'X' then acc + 1 else acc) 0) * 
  (if double then 2 else 1)
-- </vc-definitions>

-- <vc-theorems>
theorem shoot_returns_valid_result (results : GameResults) :
  shoot results = "Pete Wins!" ∨ 
  shoot results = "Phil Wins!" ∨
  shoot results = "Draw!" := sorry

theorem shoot_gives_correct_winner (results : GameResults) :
  let peteScore := results.foldl 
    (fun acc (round, double) => acc + calculateScore round.P1 double) 0
  let philScore := results.foldl 
    (fun acc (round, double) => acc + calculateScore round.P2 double) 0
  (peteScore > philScore → shoot results = "Pete Wins!") ∧
  (philScore > peteScore → shoot results = "Phil Wins!") ∧
  (peteScore = philScore → shoot results = "Draw!") := sorry

theorem shoot_symmetrical_draw (results : GameResults) :
  let symmetricalResults := results.map 
    (fun (round, double) => ({P1 := round.P1, P2 := round.P1}, double))
  shoot symmetricalResults = "Draw!" := sorry

/-
info: 'Pete Wins!'
-/
-- #guard_msgs in
-- #eval shoot [[{"P1": "XX", "P2": "XO"}, True], [{"P1": "OX", "P2": "OO"}, False], [{"P1": "XX", "P2": "OX"}, True]]

/-
info: 'Draw!'
-/
-- #guard_msgs in
-- #eval shoot [[{"P1": "XX", "P2": "XX"}, True], [{"P1": "OO", "P2": "OO"}, False], [{"P1": "XX", "P2": "XX"}, True]]

/-
info: 'Phil Wins!'
-/
-- #guard_msgs in
-- #eval shoot [[{"P1": "XX", "P2": "XO"}, False], [{"P1": "OX", "P2": "XX"}, False], [{"P1": "OO", "P2": "XX"}, True]]
-- </vc-theorems>