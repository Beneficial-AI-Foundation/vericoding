-- <vc-preamble>
def Heap := List Int

def ins (l : Heap) (x : Int) : Heap := sorry
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def pop (l : Heap) : Int × Heap := sorry

/- The heap maintains the min-heap property after insertions -/
-- </vc-definitions>

-- <vc-theorems>
theorem heap_maintains_min_property {h : Heap} (xs : List Int) : 
  let h' := xs.foldl (fun acc x => ins acc x) h
  ∀ i, 2 ≤ i → i < h'.length → 
    match h'.get? i, h'.get? (i/2) with
    | some vi, some vp => vi ≥ vp
    | _, _ => True := sorry

/- The heap extracts elements in sorted order -/

theorem heap_gives_sorted_output {h : Heap} (xs : List Int) :
  let h' := xs.foldl (fun acc x => ins acc x) h
  let rec extract (h : Heap) (n : Nat) : List Int :=
    match n with
    | 0 => []
    | n+1 => match pop h with
      | (x, h') => x :: extract h' n
  ∀ i j xi xj, i < j → j < (extract h' h'.length).length → 
    (extract h' h'.length).get? i = some xi →
    (extract h' h'.length).get? j = some xj →
    xi ≤ xj := sorry

/- Single value insertion and extraction works correctly -/

theorem heap_single_value (x : Int) :
  let h := ins [] x
  pop h = (x, []) := sorry

/-
info: 8
-/
-- #guard_msgs in
-- #eval solve_election 3 [[1, 5], [2, 10], [2, 8]]

/-
info: 0
-/
-- #guard_msgs in
-- #eval solve_election 7 [[0, 1], [3, 1], [1, 1], [6, 1], [1, 1], [4, 1], [4, 1]]

/-
info: 7
-/
-- #guard_msgs in
-- #eval solve_election 6 [[2, 6], [2, 3], [2, 8], [2, 7], [4, 4], [5, 5]]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded