-- <vc-preamble>
def find_petersen_walk : List Letter → Option (List Nat) :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isAdjacent (v1 v2: Nat) : Bool :=
  match v1, v2 with
  | 0, n => n = 1 ∨ n = 4 ∨ n = 5
  | 1, n => n = 0 ∨ n = 2 ∨ n = 6
  | 2, n => n = 1 ∨ n = 3 ∨ n = 7
  | 3, n => n = 2 ∨ n = 4 ∨ n = 8
  | 4, n => n = 0 ∨ n = 3 ∨ n = 9
  | 5, n => n = 0 ∨ n = 7 ∨ n = 8
  | 6, n => n = 1 ∨ n = 8 ∨ n = 9
  | 7, n => n = 2 ∨ n = 5 ∨ n = 9
  | 8, n => n = 3 ∨ n = 5 ∨ n = 6
  | 9, n => n = 4 ∨ n = 6 ∨ n = 7
  | _, _ => false
-- </vc-definitions>

-- <vc-theorems>
theorem petersen_walk_properties (input: List Letter) :
  match find_petersen_walk input with
  | none => True 
  | some result => 
    -- Length matches
    result.length = input.length ∧
    -- First vertex validation
    (match input.head? with
     | none => True
     | some Letter.A => result.head? = some 0 ∨ result.head? = some 5
     | some Letter.B => result.head? = some 1 ∨ result.head? = some 6 
     | some Letter.C => result.head? = some 2 ∨ result.head? = some 7
     | some Letter.D => result.head? = some 3 ∨ result.head? = some 8
     | some Letter.E => result.head? = some 4 ∨ result.head? = some 9)
  := sorry

theorem adjacent_vertices (input: List Letter) :
  match find_petersen_walk input with
  | none => True
  | some result =>
    input.length ≥ 2 →
    ∀ i, i < result.length - 1 →
      match result.get? i, result.get? (i+1) with
      | some v1, some v2 => isAdjacent v1 v2
      | _, _ => False
  := sorry

theorem minimum_path (input: List Letter) (h: input.length > 0) :
  match find_petersen_walk input with
  | none => True
  | some result =>
    match input.head?, result.head? with
    | some Letter.A, some n => n = 0 ∨ n = 5
    | some Letter.B, some n => n = 1 ∨ n = 6
    | some Letter.C, some n => n = 2 ∨ n = 7
    | some Letter.D, some n => n = 3 ∨ n = 8
    | some Letter.E, some n => n = 4 ∨ n = 9
    | _, _ => False
  := sorry
-- </vc-theorems>