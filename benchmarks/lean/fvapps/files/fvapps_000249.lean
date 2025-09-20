-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sum (l : List Nat) : Nat :=
sorry

def listMax (l : List Nat) : Nat :=
sorry

def findMinMoves (machines : List Nat) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_min_moves_non_negative
  {machines : List Nat}
  (h : findMinMoves machines ≠ -1) :
  findMinMoves machines ≥ 0 :=
sorry

theorem find_min_moves_preserves_sum
  {machines : List Nat}
  (h : findMinMoves machines ≠ -1) :
  sum machines = machines.length * (sum machines / machines.length) :=
sorry

theorem find_min_moves_lower_bound
  {machines : List Nat}
  (h : findMinMoves machines ≠ -1) :
  findMinMoves machines ≥
    max (listMax machines - sum machines / machines.length) 0 :=
sorry

theorem find_min_moves_negative_one
  {machines : List Nat}
  (h : findMinMoves machines = -1) :
  sum machines % machines.length ≠ 0 :=
sorry
-- </vc-theorems>