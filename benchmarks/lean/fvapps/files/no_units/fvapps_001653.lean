-- <vc-preamble>
def isValidMaze (maze : List String) : Bool := sorry
def hasExit (maze : List String) : Bool := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isKateAt (maze : List String) (i j : Nat) : Bool := sorry

theorem maze_properties (maze : List String) 
  (h1 : isValidMaze maze = true)
  (kateCount : Nat)
  (h2 : kateCount = 1) :
  hasExit maze = true ∨ hasExit maze = false := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem invalid_maze_no_kate (maze : List String)
  (h1 : isValidMaze maze = true)
  (kateCount : Nat)
  (h2 : kateCount = 0) :
  ∃ e, hasExit maze = e → False := sorry

theorem edge_escape (maze : List String)
  (h1 : isValidMaze maze = true)
  (kateCount : Nat)
  (h2 : kateCount = 1)
  (h3 : ∃ (i j : Nat), 
    (i = 0 ∨ i = maze.length - 1 ∨ j = 0 ∨ j = (maze.get! 0).length - 1) ∧
    isKateAt maze i j = true) :
  hasExit maze = true := sorry
-- </vc-theorems>