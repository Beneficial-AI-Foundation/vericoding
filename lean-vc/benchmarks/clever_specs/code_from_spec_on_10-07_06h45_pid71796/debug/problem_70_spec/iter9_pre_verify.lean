def problem_spec
-- function signature
(implementation: List Int → List Int)
-- inputs
(lst: List Int) :=
-- spec
let spec (result: List Int) :=
  let sorted_lst := lst.mergeSort (fun a b => decide (a ≤ b));
  (List.Perm lst result)
  ∧ (∀ i, (0 ≤ i ∧ i < lst.length ∧ i % 2 = 0) → result[i]?.getD 0 = sorted_lst[i / 2]?.getD 0)
  ∧ (∀ i, (0 ≤ i ∧ i < lst.length ∧ i % 2 = 1) → result[i]?.getD 0 = sorted_lst[lst.length - (i-1)/2 - 1]?.getD 0)
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
lemma interleave_perm (left right: List Int) :
  List.Perm (left ++ right) (interleave left right) := by
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

-- LLM HELPER
lemma take_drop_append (lst: List Int) (n: Nat) :
  lst.take n ++ lst.drop n = lst := by
  exact List.take_append_drop _ _

-- LLM HELPER
lemma interleave_get_even (left right: List Int) (i: Nat) 
  (h1: i < (interleave left right).length) (h2: i % 2 = 0) :
  (interleave left right)[i]?.getD 0 = left[i / 2]?.getD 0 := by
  generalize h : interleave left right = result
  induction left, right using interleave.induct generalizing i with
  | case1 => simp [interleave] at h; rw [h]; simp
  | case2 x xs => 
    simp [interleave] at h
    if hi : i = 0 then
      simp [hi]; rw [h]; simp
    else
      have : i ≥ 1 := Nat.one_le_iff_ne_zero.mpr hi
      rw [h]
      simp [List.getElem?_cons_succ (n := i - 1)]
      have : (i - 1) % 2 = 0 := by
        have : i = 1 + (i - 1) := by omega
        rw [this] at h2
        rw [Nat.add_mod] at h2
        simp at h2
        exact h2
      apply interleave_get_even
      rw [←h, interleave_length] at h1
      simp at h1
      omega
      exact this
  | case3 y ys => 
    simp [interleave] at h
    if hi : i = 0 then
      simp [hi] at h2
    else
      have : i ≥ 1 := Nat.one_le_iff_ne_zero.mpr hi
      rw [h]
      simp [List.getElem?_cons_succ (n := i - 1)]
      have : (i - 1) % 2 = 0 := by
        have : i = 1 + (i - 1) := by omega
        rw [this] at h2
        rw [Nat.add_mod] at h2
        simp at h2
        exact h2
      apply interleave_get_even
      rw [←h, interleave_length] at h1
      simp at h1
      omega
      exact this
  | case4 x xs y ys ih => 
    simp [interleave] at h
    if hi : i = 0 then
      simp [hi]; rw [h]; simp
    else if hi2 : i = 1 then
      simp [hi2] at h2
    else
      have : i ≥ 2 := by omega
      rw [h]
      simp [List.getElem?_cons_succ (n := i - 1)]
      simp [List.getElem?_cons_succ (n := i - 2)]
      have : (i - 2) % 2 = 0 := by
        have : i = 2 + (i - 2) := by omega
        rw [this] at h2
        rw [Nat.add_mod] at h2
        simp at h2
        exact h2
      have ih_result := ih (i - 2)
      apply ih_result
      rw [←h, interleave_length] at h1
      simp at h1
      omega
      exact this
      rfl

-- LLM HELPER  
lemma interleave_get_odd (left right: List Int) (i: Nat)
  (h1: i < (interleave left right).length) (h2: i % 2 = 1) :
  (interleave left right)[i]?.getD 0 = right[(i - 1) / 2]?.getD 0 := by
  generalize h : interleave left right = result
  induction left, right using interleave.induct generalizing i with
  | case1 => simp [interleave] at h; rw [h]; simp
  | case2 x xs => 
    simp [interleave] at h
    if hi : i = 0 then
      simp [hi] at h2
    else
      have : i ≥ 1 := Nat.one_le_iff_ne_zero.mpr hi
      rw [h]
      simp [List.getElem?_cons_succ (n := i - 1)]
      have : (i - 1) % 2 = 1 := by
        have : i = 1 + (i - 1) := by omega
        rw [this] at h2
        rw [Nat.add_mod] at h2
        simp at h2
        exact h2
      apply interleave_get_odd
      rw [←h, interleave_length] at h1
      simp at h1
      omega
      exact this
  | case3 y ys => 
    simp [interleave] at h
    if hi : i = 0 then
      simp [hi] at h2
    else
      have : i ≥ 1 := Nat.one_le_iff_ne_zero.mpr hi
      rw [h]
      simp [List.getElem?_cons_succ (n := i - 1)]
      have : (i - 1) % 2 = 1 := by
        have : i = 1 + (i - 1) := by omega
        rw [this] at h2
        rw [Nat.add_mod] at h2
        simp at h2
        exact h2
      apply interleave_get_odd
      rw [←h, interleave_length] at h1
      simp at h1
      omega
      exact this
  | case4 x xs y ys ih => 
    simp [interleave] at h
    if hi : i = 0 then
      simp [hi] at h2
    else if hi2 : i = 1 then
      simp [hi2]; rw [h]; simp
    else
      have : i ≥ 2 := by omega
      rw [h]
      simp [List.getElem?_cons_succ (n := i - 1)]
      simp [List.getElem?_cons_succ (n := i - 2)]
      have : (i - 2) % 2 = 1 := by
        have : i = 2 + (i - 2) := by omega
        rw [this] at h2
        rw [Nat.add_mod] at h2
        simp at h2
        exact h2
      have ih_result := ih (i - 2)
      apply ih_result
      rw [←h, interleave_length] at h1
      simp at h1
      omega
      exact this
      rfl

-- LLM HELPER
lemma reverse_get (lst: List Int) (i: Nat) (h: i < lst.length) :
  lst.reverse[i]?.getD 0 = lst[lst.length - 1 - i]?.getD 0 := by
  rw [List.getElem?_reverse]
  simp [h]

-- LLM HELPER
lemma mergeSort_perm (lst: List Int) : 
  List.Perm lst (lst.mergeSort (fun a b => decide (a ≤ b))) := by
  exact List.perm_mergeSort

theorem correctness
(lst: List Int)
: problem_spec implementation lst := by
  simp [problem_spec]
  use implementation lst
  constructor
  · rfl
  · simp [implementation]
    let sorted_lst := lst.mergeSort (fun a b => decide (a ≤ b))
    let n := lst.length
    let first_half := sorted_lst.take ((n + 1) / 2)
    let second_half := sorted_lst.drop ((n + 1) / 2)
    constructor
    · -- Permutation property
      have h1: List.Perm lst sorted_lst := mergeSort_perm lst
      have h2: List.Perm sorted_lst (first_half ++ second_half) := by
        rw [←take_drop_append sorted_lst ((n + 1) / 2)]
        exact List.Perm.refl _
      have h3: List.Perm (first_half ++ second_half) (interleave first_half second_half.reverse) := by
        exact interleave_perm first_half second_half.reverse
      exact List.Perm.trans h1 (List.Perm.trans h2 h3)
    · constructor
      · -- Even indices
        intro i h
        have h_len: i < (interleave first_half second_half.reverse).length := by
          rw [interleave_length]
          simp [List.length_take, List.length_drop, List.length_reverse]
          have : first_half.length + second_half.length = n := by
            simp [List.length_take, List.length_drop]
            omega
          rw [this]
          exact h.2.1
        rw [interleave_get_even first_half second_half.reverse i h_len h.2.2]
        simp [List.length_take]
        rfl
      · -- Odd indices  
        intro i h
        have h_len: i < (interleave first_half second_half.reverse).length := by
          rw [interleave_length]
          simp [List.length_take, List.length_drop, List.length_reverse]
          have : first_half.length + second_half.length = n := by
            simp [List.length_take, List.length_drop]
            omega
          rw [this]
          exact h.2.1
        rw [interleave_get_odd first_half second_half.reverse i h_len h.2.2]
        simp [List.length_drop, List.length_reverse]
        rw [reverse_get]
        · simp [List.length_drop]
          congr 1
          omega
        · simp [List.length_drop]
          omega