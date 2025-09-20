-- <vc-preamble>
def PizzaGrid := List String

def count_ones (s : String) : Nat :=
  s.toList.countP (· = '1')

def left_side (n : Nat) (row : String) : String :=
  row.take (n/2)

def right_side (n : Nat) (row : String) : String :=
  row.drop (n/2)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_pizza_balance (n : Nat) (grid : PizzaGrid) : Nat := sorry

def valid_grid (n : Nat) (grid : PizzaGrid) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem valid_output {n : Nat} {grid : PizzaGrid}
  (h : valid_grid n grid = true) :
  ∃ result : Nat, solve_pizza_balance n grid = result :=
sorry

theorem balanced_grid {n : Nat} {grid : PizzaGrid}
  (h1 : valid_grid n grid = true)
  (h2 : n % 2 = 0)
  (h3 : (List.foldl (λ acc row => acc + count_ones (left_side n row)) 0 grid) =
        (List.foldl (λ acc row => acc + count_ones (right_side n row)) 0 grid)) :
  solve_pizza_balance n grid = 0 :=
sorry

theorem minimum_difference {n : Nat} {grid : PizzaGrid}
  (h1 : valid_grid n grid = true)
  (h2 : n % 2 = 0) :
  solve_pizza_balance n grid ≤
    (List.foldl
      (λ acc row =>
        let l := count_ones (left_side n row)
        let r := count_ones (right_side n row)
        acc + if l ≥ r then l - r else r - l)
      0 grid) :=
sorry
-- </vc-theorems>