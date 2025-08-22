def problem_spec
-- function signature
(implementation: List Int → List Int)
-- inputs
(lst: List Int) :=
-- spec
let spec (result: List Int) :=
  let sorted_lst := lst.mergeSort (fun a b => decide (a ≤ b));
  (List.Perm lst result)
  ∧ (∀ i, (0 ≤ i ∧ i < lst.length ∧ i % 2 = 0) → result[i]? = sorted_lst[i / 2]?)
  ∧ (∀ i, (0 ≤ i ∧ i < lst.length ∧ i % 2 = 1) → result[i]? = sorted_lst[lst.length - (i-1)/2 - 1]?)
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
  let sorted_lst := lst.mergeSort (fun a b => decide (a ≤ b))
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
  (interleave left right)[i]? = left[i / 2]? := by
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
        | succ m => simp at h2; rw [ih]; simp; ring_nf
    | cons y ys =>
      simp [interleave] at h1 h2 ⊢
      cases i with
      | zero => simp
      | succ n =>
        cases n with
        | zero => simp at h2
        | succ m => simp at h2; rw [ih]; simp; ring_nf

-- LLM HELPER
lemma interleave_get_odd (left right: List Int) (i: Nat) 
  (h1: i < (interleave left right).length) (h2: i % 2 = 1) :
  (interleave left right)[i]? = right[(i - 1) / 2]? := by
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
        | succ m => simp at h2; ring_nf
  | cons x xs ih =>
    cases right with
    | nil => 
      simp [interleave] at h1 h2 ⊢
      cases i with
      | zero => simp at h2
      | succ n => 
        cases n with
        | zero => simp
        | succ m => simp at h2; rw [ih]; simp; ring_nf
    | cons y ys =>
      simp [interleave] at h1 h2 ⊢
      cases i with
      | zero => simp at h2
      | succ n =>
        cases n with
        | zero => simp
        | succ m => simp at h2; rw [ih]; simp; ring_nf

-- LLM HELPER
lemma interleave_perm (left right: List Int) : 
  List.Perm (left ++ right) (interleave left right) := by
  induction left generalizing right with
  | nil => 
    simp [interleave]
  | cons x xs ih =>
    cases right with
    | nil => 
      simp [interleave, List.append_nil]
    | cons y ys =>
      simp [interleave]
      have h1 : List.Perm (x :: xs ++ y :: ys) (x :: y :: xs ++ ys) := by
        rw [List.perm_cons_iff]
        exact List.perm_append_comm.trans (List.perm_cons_append_cons List.Perm.refl)
      exact List.Perm.trans h1 (List.perm_cons_cons ih)

-- LLM HELPER
lemma take_drop_append (lst: List Int) (n: Nat) : 
  lst.take n ++ lst.drop n = lst := List.take_append_drop _ _

-- LLM HELPER
lemma sorted_reverse_index (lst: List Int) (i: Nat) (h: i < lst.length) :
  lst.reverse[i]? = lst[lst.length - 1 - i]? := by
  rw [List.get?_reverse']
  simp only [List.length_reverse]
  rw [if_pos h]

theorem correctness
(lst: List Int)
: problem_spec implementation lst := by
  simp [problem_spec, implementation]
  let sorted_lst := lst.mergeSort (fun a b => decide (a ≤ b))
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
        rw [take_drop_append]
      have h3 : List.Perm (left_half ++ right_half.reverse) (left_half ++ right_half) := by
        rw [List.perm_append_left_iff]
        exact List.perm_reverse
      have h4 : List.Perm lst (left_half ++ right_half.reverse) := by
        exact List.Perm.trans h1 (List.Perm.trans h2 h3)
      exact List.Perm.trans h4 (interleave_perm left_half right_half.reverse)
    · constructor
      · -- Prove even indices
        intros i h
        have h_len : result.length = lst.length := by
          rw [interleave_length]
          simp [List.length_take, List.length_drop, List.length_reverse]
          simp [List.length_mergeSort]
          have : sorted_lst.length = lst.length := List.length_mergeSort
          rw [this]
          rw [List.length_take, List.length_drop, min_def]
          split_ifs with h_le
          · simp [Nat.add_sub_cancel']
          · simp [Nat.add_sub_cancel']
        rw [← h_len] at h
        exact interleave_get_even left_half right_half.reverse i h.2.1 h.2.2
      · -- Prove odd indices  
        intros i h
        have h_len : result.length = lst.length := by
          rw [interleave_length]
          simp [List.length_take, List.length_drop, List.length_reverse]
          simp [List.length_mergeSort]
          have : sorted_lst.length = lst.length := List.length_mergeSort
          rw [this]
          rw [List.length_take, List.length_drop, min_def]
          split_ifs with h_le
          · simp [Nat.add_sub_cancel']
          · simp [Nat.add_sub_cancel']
        rw [← h_len] at h
        have h_odd := interleave_get_odd left_half right_half.reverse i h.2.1 h.2.2
        rw [h_odd]
        rw [sorted_reverse_index]
        · simp [List.length_reverse]
          ring_nf
        · simp [List.length_reverse]
          have h_div : (i - 1) / 2 < right_half.length := by
            simp [List.length_drop]
            rw [List.length_mergeSort]
            apply Nat.div_lt_iff_lt_mul
            · norm_num
            · linarith
          exact h_div