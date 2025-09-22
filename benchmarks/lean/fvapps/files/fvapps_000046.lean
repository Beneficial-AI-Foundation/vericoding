-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_rock_paper_scissors (s: String) : String :=
sorry

def beats (move1 move2 : Char) : Bool :=
sorry

def getMostFrequentMove (s : String) : Char :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem length_preservation (s : String) :
  s.length > 0 → (solve_rock_paper_scissors s).length = s.length :=
sorry

theorem valid_moves (s : String) (i : String.Pos) :
  s.length > 0 →
  (solve_rock_paper_scissors s).get i = 'R' ∨
  (solve_rock_paper_scissors s).get i = 'P' ∨
  (solve_rock_paper_scissors s).get i = 'S' :=
sorry

theorem uniform_response (s : String) :
  s.length > 0 → ∀ i j : String.Pos,
  (solve_rock_paper_scissors s).get i = (solve_rock_paper_scissors s).get j :=
sorry

theorem beats_most_frequent (s : String) (h: s.length > 0):
  let mostFrequent := getMostFrequentMove s
  let firstChar := (solve_rock_paper_scissors s).front
  beats firstChar mostFrequent :=
sorry
-- </vc-theorems>