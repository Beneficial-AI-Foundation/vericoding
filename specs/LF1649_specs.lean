-- <vc-preamble>
def getMatchingPieces (pieces: List Piece) : Piece → Bool := sorry
def checkFit (p1 p2: Piece) (dir: String) : Bool := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def puzzleSolver (pieces: List Piece) (width height: Nat) : Option (List (List Nat)) := sorry

theorem getMatchingPieces_preserves_length (pieces: List Piece):
  pieces.length = (pieces.filter (getMatchingPieces pieces)).length := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem getMatchingPieces_contains_all_ids (pieces: List Piece) (p: Piece):
  p ∈ pieces → p ∈ (pieces.filter (getMatchingPieces pieces)) := sorry

theorem checkFit_returns_bool (p1 p2: Piece) (dir: String):
  checkFit p1 p2 dir = true ∨ checkFit p1 p2 dir = false := sorry

theorem checkFit_right (p1 p2: Piece):
  checkFit p1 p2 "right" = (p1.right + p2.left = 0) := sorry

theorem checkFit_down (p1 p2: Piece): 
  checkFit p1 p2 "down" = (p1.down + p2.up = 0) := sorry

theorem checkFit_invalid (p1 p2: Piece) (dir: String):
  dir ≠ "right" → dir ≠ "down" → checkFit p1 p2 dir = false := sorry

theorem puzzleSolver_result_dimensions {pieces: List Piece} {width height: Nat}
  (result: Option (List (List Nat))):
  result = puzzleSolver pieces width height →
  result.isSome → 
  match result with
  | none => True
  | some grid => grid.length = height ∧ grid.all (fun row => row.length = width)
  := sorry

theorem puzzleSolver_uses_valid_pieces {pieces: List Piece} {width height: Nat}
  (result: Option (List (List Nat))):
  result = puzzleSolver pieces width height →
  result.isSome →
  match result with
  | none => True  
  | some grid => ∀ id ∈ grid.join, ∃ p ∈ pieces, p.id = id
  := sorry

theorem puzzleSolver_pieces_fit {pieces: List Piece} {width height: Nat}
  (result: Option (List (List Nat))):
  result = puzzleSolver pieces width height →
  result.isSome →
  match result with
  | none => True
  | some grid =>
    ∀ y x: Nat, y < height → x < width →
    if x > 0 ∧ grid[y]?.isSome ∧ Option.isSome (grid[y]? >>= (·[x]?)) ∧ Option.isSome (grid[y]? >>= (·[x-1]?))
    then match grid[y]?, grid[y]? >>= (·[x]?), grid[y]? >>= (·[x-1]?) with
      | some row, some curr, some prev =>
        match pieces.find? (·.id = curr), pieces.find? (·.id = prev) with
        | some currPiece, some prevPiece => checkFit prevPiece currPiece "right"
        | _, _ => false
      | _, _, _ => false
    else if y > 0 ∧ grid[y]?.isSome ∧ Option.isSome (grid[y]? >>= (·[x]?)) ∧ Option.isSome (grid[y-1]? >>= (·[x]?))
    then match grid[y]?, grid[y]? >>= (·[x]?), grid[y-1]? >>= (·[x]?) with
      | some row, some curr, some above =>
        match pieces.find? (·.id = curr), pieces.find? (·.id = above) with
        | some currPiece, some abovePiece => checkFit abovePiece currPiece "down"
        | _, _ => false
      | _, _, _ => false
    else true
  := sorry
-- </vc-theorems>