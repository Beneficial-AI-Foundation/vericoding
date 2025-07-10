def problem_spec
-- function signature
(implementation: List Int → List Int)
-- inputs
(lst: List Int) :=
-- spec
let spec (result: List Int) :=
  let sorted_lst := lst.mergeSort;
  (List.Perm lst result)
  ∧ (forall i, (0 <= i ∧ i < lst.length ∧ i % 2 = 0) → result[i]! = sorted_lst[i / 2]!)
  ∧ (forall i, (0 <= i ∧ i < lst.length ∧ i % 2 = 1) → result[i]! = sorted_lst[lst.length - (i-1)/2 - 1]!)
-- program termination
∃ result, implementation lst = result ∧ spec result

-- LLM HELPER
def interleave (left: List Int) (right: List Int) : List Int :=
  match left, right with
  | [], [] => []
  | x :: xs, [] => x :: interleave xs []
  | [], y :: ys => y :: interleave [] ys
  | x :: xs, y :: ys => x :: y :: interleave xs ys

def implementation (lst: List Int): List Int := 
  let sorted_lst := lst.mergeSort
  let n := sorted_lst.length
  let left_half := sorted_lst.take ((n + 1) / 2)
  let right_half := sorted_lst.drop ((n + 1) / 2)
  interleave left_half right_half.reverse

-- LLM HELPER
lemma interleave_length (left right: List Int) : 
  (interleave left right).length = left.length + right.length := by
  induction left generalizing right with
  | nil => 
    induction right with
    | nil => simp [interleave]
    | cons y ys ih => simp [interleave]; rw [ih]; simp
  | cons x xs ih =>
    cases right with
    | nil => simp [interleave, ih]
    | cons y ys => simp [interleave]; rw [ih]; simp

-- LLM HELPER
lemma interleave_get_even (left right: List Int) (i: Nat) 
  (h1: i < (interleave left right).length) (h2: i % 2 = 0) :
  (interleave left right)[i]! = left[i / 2]! := by
  induction left generalizing right i with
  | nil => 
    cases right with
    | nil => simp [interleave] at h1
    | cons y ys => 
      simp [interleave] at h1 h2 ⊢
      cases i with
      | zero => simp at h2
      | succ n => simp at h2
  | cons x xs ih =>
    cases right with
    | nil => 
      simp [interleave] at h1 h2 ⊢
      cases i with
      | zero => simp
      | succ n => 
        simp at h2 ⊢
        cases n with
        | zero => simp at h2
        | succ m => simp at h2; rw [ih]; simp
    | cons y ys =>
      simp [interleave] at h1 h2 ⊢
      cases i with
      | zero => simp
      | succ n =>
        cases n with
        | zero => simp at h2
        | succ m => simp at h2; rw [ih]; simp

-- LLM HELPER
lemma interleave_get_odd (left right: List Int) (i: Nat) 
  (h1: i < (interleave left right).length) (h2: i % 2 = 1) :
  (interleave left right)[i]! = right[(i - 1) / 2]! := by
  induction left generalizing right i with
  | nil => 
    cases right with
    | nil => simp [interleave] at h1
    | cons y ys => 
      simp [interleave] at h1 h2 ⊢
      cases i with
      | zero => simp at h2
      | succ n => 
        cases n with
        | zero => simp
        | succ m => simp at h2; sorry
  | cons x xs ih =>
    cases right with
    | nil => 
      simp [interleave] at h1 h2 ⊢
      cases i with
      | zero => simp at h2
      | succ n => 
        cases n with
        | zero => simp
        | succ m => simp at h2; sorry
    | cons y ys =>
      simp [interleave] at h1 h2 ⊢
      cases i with
      | zero => simp at h2
      | succ n =>
        cases n with
        | zero => simp
        | succ m => simp at h2; rw [ih]; simp

-- LLM HELPER
lemma interleave_perm (left right: List Int) (l: List Int) 
  (h1: List.Perm l (left ++ right)) : 
  List.Perm l (interleave left right) := by
  rw [List.perm_comm] at h1 ⊢
  induction left generalizing right l with
  | nil => 
    simp [interleave]
    rwa [List.nil_append] at h1
  | cons x xs ih =>
    cases right with
    | nil => 
      simp [interleave, List.append_nil] at h1 ⊢
      exact h1
    | cons y ys =>
      simp [interleave]
      have h2 : List.Perm (x :: y :: xs ++ ys) (left ++ right) := by
        simp [List.append_cons]
        exact List.perm_cons_append_cons h1
      sorry

theorem correctness
(lst: List Int)
: problem_spec implementation lst := by
  simp [problem_spec, implementation]
  let sorted_lst := lst.mergeSort
  let n := sorted_lst.length
  let left_half := sorted_lst.take ((n + 1) / 2)
  let right_half := sorted_lst.drop ((n + 1) / 2)
  let result := interleave left_half right_half.reverse
  
  use result
  constructor
  · rfl
  · constructor
    · -- Prove permutation
      have h1 : List.Perm lst sorted_lst := List.perm_mergeSort
      have h2 : List.Perm sorted_lst (left_half ++ right_half) := by
        rw [List.take_append_drop]
      have h3 : List.Perm (left_half ++ right_half.reverse) (left_half ++ right_half) := by
        rw [List.perm_append_left_iff]
        exact List.perm_reverse
      have h4 : List.Perm lst (left_half ++ right_half.reverse) := by
        exact List.Perm.trans h1 (List.Perm.trans h2 h3)
      exact interleave_perm left_half right_half.reverse lst h4
    · constructor
      · -- Prove even indices
        intros i h
        have h_len : result.length = lst.length := by
          rw [interleave_length]
          simp [List.length_take, List.length_drop, List.length_reverse]
          simp [List.length_mergeSort]
          sorry
        rw [← h_len] at h
        exact interleave_get_even left_half right_half.reverse i h.left h.right.right
      · -- Prove odd indices  
        intros i h
        have h_len : result.length = lst.length := by
          rw [interleave_length]
          simp [List.length_take, List.length_drop, List.length_reverse]
          simp [List.length_mergeSort]
          sorry
        rw [← h_len] at h
        have h_odd := interleave_get_odd left_half right_half.reverse i h.left h.right.right
        simp at h_odd
        exact h_odd