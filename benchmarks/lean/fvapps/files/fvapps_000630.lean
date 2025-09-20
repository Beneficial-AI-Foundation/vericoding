-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isValidGrid (grid : List (List Char)) : Bool :=
  sorry

def countOnes (grid : List (List Char)) : Nat :=
  sorry

def isGravityConsistent (grid : List (List Char)) (force : Char) : Bool :=
  sorry

def solveParticleGrid (n m : Nat) (grid : List (List Char)) (forces : List Char) : List (List Char) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem grid_dimensions {n m : Nat} {grid : List (List Char)} {forces : List Char}
  (h1 : isValidGrid grid) :
  let result := solveParticleGrid n m grid forces
  List.length result = n ∧
  ∀ row ∈ result, List.length row = m :=
sorry

theorem grid_valid_chars {n m : Nat} {grid : List (List Char)} {forces : List Char}
  (h1 : isValidGrid grid) :
  let result := solveParticleGrid n m grid forces
  ∀ row ∈ result, ∀ c ∈ row, c = '0' ∨ c = '1' :=
sorry

theorem preserved_ones_count {n m : Nat} {grid : List (List Char)} {forces : List Char}
  (h1 : isValidGrid grid) :
  let result := solveParticleGrid n m grid forces
  countOnes grid = countOnes result :=
sorry

theorem final_gravity_consistent {n m : Nat} {grid : List (List Char)} {forces : List Char}
  (h1 : isValidGrid grid)
  (h2 : forces ≠ []) :
  let result := solveParticleGrid n m grid forces
  let lastForce := List.getLast forces h2
  isGravityConsistent result lastForce :=
sorry
-- </vc-theorems>