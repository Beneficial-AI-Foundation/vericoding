-- <vc-preamble>
def find_course_order (numCourses : Nat) (prerequisites : List (Nat × Nat)) : List Nat :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isSorted (l : List Nat) : Prop :=
  ∀ i j, i < j → j < l.length → l[i]! ≤ l[j]!
-- </vc-definitions>

-- <vc-theorems>
theorem empty_prerequisites (n : Nat) (h : 0 < n) :
  let result := find_course_order n []
  (result.length = n) ∧ 
  (isSorted result) ∧
  (∀ i < n, i ∈ result) := by
  sorry

theorem prerequisites_in_range (n : Nat) (prereqs : List (Nat × Nat)) (h : 0 < n) :
  let valid_prereqs := prereqs.filter (fun p => p.1 < n ∧ p.2 < n)
  let result := find_course_order n valid_prereqs
  result.length ≠ 0 → 
  (result.length = n) ∧
  (isSorted result) ∧
  (∀ i < n, i ∈ result) ∧
  (∀ course, ∀ post pre, 
    course ∈ result →
    (post, pre) ∈ valid_prereqs →
    post = course → 
    pre ∈ (result.take (result.indexOf course))) := by
  sorry

theorem cycle_detection (n : Nat) (h : 1 < n) :
  let cyclic_prereqs := 
    (List.range (n-1)).map (fun i => (i+1, i)) ++ [(0, n-1)]
  find_course_order n cyclic_prereqs = [] := by
  sorry

theorem linear_chain (n : Nat) (h : 0 < n) :
  let linear_prereqs := 
    (List.range (n-1)).map (fun i => (i+1, i))
  find_course_order n linear_prereqs = List.range n := by
  sorry

/-
info: [0, 1]
-/
-- #guard_msgs in
-- #eval find_course_order 2 [[1, 0]]

/-
info: []
-/
-- #guard_msgs in
-- #eval find_course_order 2 [[1, 0], [0, 1]]
-- </vc-theorems>