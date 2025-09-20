-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def longestWPI (hours : List Nat) : Nat := sorry

theorem longestWPI_non_negative (hours : List Nat) : 
  longestWPI hours ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem longestWPI_bounded (hours : List Nat) :
  longestWPI hours ≤ hours.length := sorry

theorem longestWPI_empty :
  longestWPI [] = 0 := sorry

theorem longestWPI_optimal (hours : List Nat) (start len : Nat) :
  start < hours.length →
  len > longestWPI hours →
  len ≤ hours.length - start →
  let subseq := (hours.drop start).take len
  let productive := (subseq.filter (· > 8)).length 
  let tired := len - productive
  productive ≤ tired := sorry
-- </vc-theorems>