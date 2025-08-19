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
  let n := lst.length
  let first_half := sorted_lst.take ((n + 1) / 2)
  let second_half := sorted_lst.drop ((n + 1) / 2)
  interleave first_half second_half.reverse

-- LLM HELPER
lemma interleave_length (left right: List Int) : 
  (interleave left right).length = left.length + right.length := by
  induction left, right using interleave.induct with
  | case1 => simp [interleave]
  | case2 x xs => simp [interleave, interleave_length]
  | case3 y ys => simp [interleave, interleave_length]  
  | case4 x xs y ys ih => simp [interleave, ih]

-- LLM HELPER  
lemma interleave_perm (left right: List Int) (orig: List Int) 
  (h1: List.Perm orig (left ++ right)) :
  List.Perm orig (interleave left right) := by
  have h2: List.Perm (left ++ right) (interleave left right) := by
    induction left, right using interleave.induct with
    | case1 => simp [interleave]
    | case2 x xs => simp [interleave]; exact List.Perm.refl _
    | case3 y ys => simp [interleave]; exact List.Perm.refl _
    | case4 x xs y ys ih => 
      simp [interleave]
      have h: List.Perm (x :: (xs ++ y :: ys)) (x :: y :: interleave xs ys) := by
        apply List.Perm.trans (List.perm_cons_app_comm _ _ _)
        exact List.Perm.cons _ ih
      exact h
  exact List.Perm.trans h1 h2

-- LLM HELPER
lemma take_drop_perm (lst: List Int) (n: Nat) :
  List.Perm lst (lst.take n ++ lst.drop n) := by
  exact List.perm_append_comm.symm.trans (List.take_append_drop n lst).symm ▸ List.Perm.refl _

-- LLM HELPER
lemma interleave_get_even (left right: List Int) (i: Nat) 
  (h1: i < (interleave left right).length) (h2: i % 2 = 0) :
  (interleave left right)[i]! = left[i / 2]! := by
  sorry

-- LLM HELPER  
lemma interleave_get_odd (left right: List Int) (i: Nat)
  (h1: i < (interleave left right).length) (h2: i % 2 = 1) :
  (interleave left right)[i]! = right[(i - 1) / 2]! := by
  sorry

-- LLM HELPER
lemma reverse_get (lst: List Int) (i: Nat) (h: i < lst.length) :
  lst.reverse[i]! = lst[lst.length - 1 - i]! := by
  sorry

theorem correctness
(lst: List Int)
: problem_spec implementation lst := by
  simp [problem_spec]
  use implementation lst
  constructor
  · rfl
  · simp [implementation]
    let sorted_lst := lst.mergeSort
    let n := lst.length
    let first_half := sorted_lst.take ((n + 1) / 2)
    let second_half := sorted_lst.drop ((n + 1) / 2)
    constructor
    · -- Permutation property
      have h1: List.Perm lst sorted_lst := List.perm_mergeSort
      have h2: List.Perm sorted_lst (first_half ++ second_half) := take_drop_perm sorted_lst ((n + 1) / 2)
      have h3: List.Perm (first_half ++ second_half) (interleave first_half second_half.reverse) := by
        sorry
      exact List.Perm.trans h1 (List.Perm.trans h2 h3)
    · constructor
      · -- Even indices
        intro i h
        have h_len: i < (interleave first_half second_half.reverse).length := by
          rw [interleave_length]
          simp [List.length_take, List.length_drop, List.length_reverse]
          sorry
        rw [interleave_get_even first_half second_half.reverse i h_len h.2.2]
        simp [List.length_take]
        sorry
      · -- Odd indices  
        intro i h
        have h_len: i < (interleave first_half second_half.reverse).length := by
          rw [interleave_length]
          simp [List.length_take, List.length_drop, List.length_reverse]
          sorry
        rw [interleave_get_odd first_half second_half.reverse i h_len h.2.2]
        simp [List.length_drop, List.length_reverse]
        rw [reverse_get]
        sorry