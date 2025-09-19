-- <vc-preamble>
def Stone := Char 

def isRGBChar (c : Char) : Prop :=
  c = 'R' ∨ c = 'G' ∨ c = 'B'
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solution (stones : String) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solution_non_negative (stones : String) 
  (h : ∀ c ∈ stones.data, isRGBChar c) :
  solution stones ≥ 0 := sorry

theorem solution_upper_bound (stones : String)
  (h : ∀ c ∈ stones.data, isRGBChar c) :
  solution stones ≤ stones.length - 1 := sorry

theorem solution_counts_adjacents (stones : String)
  (h : ∀ c ∈ stones.data, isRGBChar c) :
  let adjacentPairs := List.range (stones.length - 1)
  let countMatches := (adjacentPairs.filter (fun i => stones.data[i]! = stones.data[i+1]!)).length
  solution stones = countMatches := sorry

theorem solution_zero_no_adjacents (stones : String)
  (h : ∀ c ∈ stones.data, isRGBChar c)
  (h2 : solution stones = 0) :
  ∀ i, i > 0 → i < stones.length →
    stones.data[i]! ≠ stones.data[i-1]! := sorry

theorem solution_all_same (stones : String)
  (h : ∀ c ∈ stones.data, isRGBChar c)  
  (h2 : stones.length > 0)
  (h3 : ∀ c ∈ stones.data, c = stones.data[0]!) :
  solution stones = stones.length - 1 := sorry

theorem solution_alternating (stones : String)
  (h : ∀ c ∈ stones.data, isRGBChar c)
  (h2 : stones.length > 1)  
  (h3 : ∀ i, i > 0 → i < stones.length →
    stones.data[i]! ≠ stones.data[i-1]!) :
  solution stones = 0 := sorry
-- </vc-theorems>