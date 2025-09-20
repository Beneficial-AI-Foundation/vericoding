-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def get_scoreboard (n : Nat) (k : Nat) (submissions : List (String × Nat)) : List String := sorry

theorem scoreboard_points_descending
  {n : Nat} {k : Nat} {submissions : List (String × Nat)}
  (h : 0 < n) :
  let result := get_scoreboard n k submissions
  let points := result.map (λ e => (e.splitOn " ").getLast!.toNat!)
  ∀ i j, i < j → j < points.length → points[i]! ≥ points[j]! := sorry
-- </vc-definitions>

-- <vc-theorems>
-- </vc-theorems>