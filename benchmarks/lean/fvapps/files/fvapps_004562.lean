-- <vc-preamble>
def VALID_COLORS := ["Red", "Blue", "Green", "Orange", "Purple", "Yellow"]

structure Game where
  solution : List String := []
  tries : Nat := 0
  deriving Repr
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Game.check (g : Game) (guess : List String) : List String :=
sorry

def matches_result (code guess result : List String) : Bool :=
sorry

def mastermind (g : Game) : Unit :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem mastermind_always_solves {solution : List String}
  (h1 : solution.length = 4)
  (h2 : ∀ x ∈ solution, x ∈ VALID_COLORS) :
  ∀ g : Game, g.solution = solution → g.tries ≤ 60 :=
sorry

theorem matches_result_symmetric {code guess : List String}
  (h1 : code.length = 4)
  (h2 : guess.length = 4)
  (h3 : ∀ x ∈ code, x ∈ VALID_COLORS)
  (h4 : ∀ x ∈ guess, x ∈ VALID_COLORS) :
  matches_result code guess (List.replicate 4 "Black") =
  matches_result guess code (List.replicate 4 "Black") :=
sorry

theorem matches_result_self {guess : List String}
  (h1 : guess.length = 4)
  (h2 : ∀ x ∈ guess, x ∈ VALID_COLORS) :
  matches_result guess guess (List.replicate 4 "Black") = true :=
sorry

theorem game_check_invalid_inputs (g : Game) :
  (∀ guess : List String, guess.length ≠ 4 → g.check guess = []) ∧
  (∀ guess : List String, (∃ x ∈ guess, x ∉ VALID_COLORS) → g.check guess = []) ∧
  (g.tries ≥ 60 → ∀ guess : List String, g.check guess = []) :=
sorry

theorem check_result_length {solution guess : List String}
  (h1 : solution.length = 4)
  (h2 : guess.length = 4)
  (h3 : ∀ x ∈ solution, x ∈ VALID_COLORS)
  (h4 : ∀ x ∈ guess, x ∈ VALID_COLORS)
  (g : Game)
  (h5 : g.solution = solution) :
  let result := g.check guess
  (result.length ≤ 4 ∧ ∀ x ∈ result, x = "Black" ∨ x = "White") :=
sorry
-- </vc-theorems>