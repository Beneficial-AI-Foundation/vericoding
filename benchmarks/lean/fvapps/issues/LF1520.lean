-- <vc-preamble>
def find (d : Dsu) (x : Nat) : Nat := sorry
def union (d : Dsu) (x y : Nat) : Dsu := sorry

def stringContainsSlash (s : String) : Bool := 
  s.any (fun c => c = '/')
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_gears (speeds : List Nat) (queries : List (List Nat)) : List String := sorry

variable (n : Nat) (speeds : List Nat) (queries : List (List Nat)) (d : Dsu)
-- </vc-definitions>

-- <vc-theorems>
theorem basic_gear_properties 
  (h1 : n ≥ 2) 
  (h2 : speeds.length ≥ 2)
  (h3 : queries.length ≥ 1) :
  let result := solve_gears speeds queries
  (∀ r ∈ result, r = "0" ∨ stringContainsSlash r) := sorry

theorem dsu_reflexivity
  (h1 : n ≥ 2)
  (h2 : speeds.length ≥ 2) :
  ∀ i < n, find d i = find d i := sorry

theorem dsu_initial_state
  (h1 : n ≥ 2)
  (h2 : speeds.length ≥ 2) :
  (∀ x ∈ d.zero, ¬x) ∧ 
  (∀ x ∈ d.dr, x = 1) := sorry

theorem dsu_union_symmetry
  (h1 : n ≥ 2)
  (h2 : speeds.length ≥ 2) :
  find (union d 0 1) 0 = find (union d 0 1) 1 := sorry

theorem three_gear_ratio
  (h1 : n ≥ 3)
  (h2 : speeds.length ≥ 3) :
  let queries := [[2, 1, 2], [2, 2, 3], [3, 1, 3, 1]]
  let result := solve_gears speeds queries
  match result.getLast? with
  | some s => s = "0" ∨ stringContainsSlash s
  | none => False := sorry
-- </vc-theorems>