import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

-- LLM HELPER
def find_coords_in_row (row : List Int) (x : Int) (row_idx : Nat) : List (Nat × Nat) :=
  (row.mapIdx (fun col_idx val => (row_idx, col_idx))).filter (fun (_, col_idx) => row.get! col_idx = x)

-- LLM HELPER
def sort_row_coords (coords : List (Nat × Nat)) (row : Nat) : List (Nat × Nat) :=
  let row_coords := coords.filter (fun (r, _) => r = row)
  row_coords.mergeSort (fun (_, c1) (_, c2) => c1 ≥ c2)

-- LLM HELPER
def sort_all_coords (coords : List (Nat × Nat)) : List (Nat × Nat) :=
  let grouped_by_row := coords.groupBy (fun (r1, _) (r2, _) => r1 = r2)
  let sorted_groups := grouped_by_row.map (fun group => 
    group.mergeSort (fun (_, c1) (_, c2) => c1 ≥ c2))
  let flattened := sorted_groups.foldl List.append []
  flattened.mergeSort (fun (r1, _) (r2, _) => r1 ≤ r2)

def implementation (lst: List (List Int)) (x: Int) : List (Nat × Nat) :=
  let all_coords := lst.mapIdx (fun row_idx row => 
    row.mapIdx (fun col_idx val => 
      if val = x then some (row_idx, col_idx) else none)
    |>.filterMap id) |>.foldl List.append []
  
  -- Sort by row ascending, then by column descending within each row
  let sorted_by_row := all_coords.mergeSort (fun (r1, c1) (r2, c2) => 
    if r1 = r2 then c1 ≥ c2 else r1 ≤ r2)
  
  sorted_by_row

def problem_spec
-- function signature
(implementation: List (List Int) → Int → List (Nat × Nat))
-- inputs
(lst: List (List Int))
(x: Int) :=
-- spec
let spec (result : List (Nat × Nat)) :=
  (∀ i, i < result.length →
    let (row, col) := result[i]!
    row < lst.length ∧
    col < lst[row]!.length ∧
    (lst[row]!)[col]! = x) ∧
  (∀ᵉ (i < lst.length) (j < lst[i]!.length),
    (lst[i]!)[j]! = x → (i, j) ∈ result) ∧
  (result.map (fun (r, _) => r)).Sorted Nat.le ∧
  (∀ i < result.length,
    let (row, _) := result[i]!
    ((result.filter (fun (r, _) => r = row)).map (fun (_, c) => c)).Sorted (fun a b => a ≥ b))
-- program termination
∃ result,
  implementation lst x = result ∧
  spec result

theorem correctness
(lst: List (List Int))
(x: Int)
: problem_spec implementation lst x
:= by
  use implementation lst x
  constructor
  · rfl
  · simp [implementation]
    sorry

-- #test implementation "Hi" = "Hi"
-- #test implementation "hello" = "ehllo"
-- #test implementation "Hello World!!!" = "Hello !!!Wdlor"