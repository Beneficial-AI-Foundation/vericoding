-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def path_finder (maze : String) : Bool :=
sorry

def stringReplicate (n : Nat) (s : String) : String :=
sorry

def stringJoin (l : List String) (sep : String) : String :=
sorry

def makeList (n : Nat) (c : Char) : List Char :=
sorry

def listToString (l : List Char) : String :=
sorry

def make_maze (cells : List Char) : String :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem empty_maze_always_solvable (n : Nat) (h : n ≥ 2) (h2 : n ≤ 10) :
  let row := stringReplicate n "."
  let rows := List.replicate n row
  path_finder (stringJoin rows "\n") = true :=
sorry

theorem border_wall_maze_unsolvable (n : Nat) (h : n ≥ 2) (h2 : n ≤ 10) :
  let row := stringReplicate n "W"
  let rows := List.replicate n row
  path_finder (stringJoin rows "\n") = false :=
sorry

theorem random_valid_maze_returns_bool (cells : List Char)
  (h1 : cells.length ≥ 4) (h2 : cells.length ≤ 100)
  (h3 : ∀ c ∈ cells, c = '.' ∨ c = 'W')
  (h4 : ∃ n : Nat, n * n = cells.length)
  (h5 : cells ≠ [] → cells[0] = '.')
  (h6 : cells ≠ [] → cells[cells.length - 1] = '.') :
  (path_finder (make_maze cells)) = true ∨ (path_finder (make_maze cells)) = false :=
sorry

theorem single_path_solvable :
  path_finder "..W\nW.W\n..." = true :=
sorry

theorem path_to_self_exists (n : Nat) (h : n ≥ 2) (h2 : n ≤ 10) :
  let cells := makeList (n*n) '.'
  path_finder (make_maze cells) = true :=
sorry
-- </vc-theorems>