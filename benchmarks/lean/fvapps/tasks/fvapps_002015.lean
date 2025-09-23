-- <vc-preamble>
def Card := Nat

def Pile := List Card
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Game := List (Nat × Pile)

def listSum (l : List Nat) : Nat :=
  sorry

def solve_card_game (g : Game) : Nat × Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_card_game_returns_tuple (g : Game) :
  let (a, b) := solve_card_game g
  a ≥ 0 ∧ b ≥ 0 :=
sorry

theorem sum_scores_equals_input (g : Game) :
  let (a, b) := solve_card_game g
  let total := g.map (fun p => listSum p.2) |> listSum
  a + b = total :=
sorry

theorem first_pile_split_correctly (g : Game) (h : g ≠ []) :
  let first := g.head h
  let k := first.1 / 2 + 1
  let first_sum := listSum first.2
  let rest_sum := g.tail.map (fun p => listSum p.2) |> listSum
  let (a, b) := solve_card_game g
  a + b = first_sum + rest_sum :=
sorry
-- </vc-theorems>