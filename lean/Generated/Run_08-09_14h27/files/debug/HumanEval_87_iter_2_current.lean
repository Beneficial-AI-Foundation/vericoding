import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

-- LLM HELPER
def List.groupByKey {α β : Type*} [DecidableEq β] (l : List α) (f : α → β) : List (List α) :=
  let keys := (l.map f).eraseDups
  keys.map (fun k => l.filter (fun x => f x = k))

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
    constructor
    · intro i hi
      simp at hi ⊢
      constructor
      constructor
      constructor
      · simp [List.mergeSort]
        apply List.length_pos.mp
        exact hi
      · simp [List.mergeSort]
        apply List.length_pos.mp  
        exact hi
      · simp [List.mergeSort]
        rfl
    constructor
    · intro i j hi hj heq
      simp [List.mem_mergeSort]
      simp [List.mem_foldl]
      simp [List.mem_mapIdx]
      use i
      constructor
      · exact hi
      · simp [List.mem_filterMap]
        use (i, j)
        constructor
        · simp [List.mem_mapIdx]
          use j
          constructor
          · exact hj
          · simp [heq]
        · simp [heq]
    constructor
    · simp [List.Sorted]
      apply List.mergeSort_sorted
    · simp [List.Sorted]
      apply List.mergeSort_sorted

-- #test implementation "Hi" = "Hi"
-- #test implementation "hello" = "ehllo"
-- #test implementation "Hello World!!!" = "Hello !!!Wdlor"