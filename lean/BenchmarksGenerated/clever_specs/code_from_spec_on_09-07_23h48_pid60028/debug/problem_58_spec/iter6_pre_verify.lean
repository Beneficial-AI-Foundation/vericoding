def problem_spec
-- function signature
(implementation: List Int → List Int → List Int)
-- inputs
(l1 l2: List Int) :=
let is_unique (result: List Int) :=
  ∀ i j, i < result.length → j < result.length →
  i ≠ j → result[i]! ≠ result[j]!;
let is_sorted (result: List Int) :=
  ∀ i, i < result.length - 1 →
  result[i]! ≤ result[i + 1]!;
-- spec
let spec (result: List Int) :=
  is_unique result ∧
  is_sorted result ∧
  (∀ i : Int, i ∈ result ↔ i ∈ l1 ∧ i ∈ l2)
-- program termination
∃ result, implementation l1 l2 = result ∧
spec result

-- LLM HELPER
def filter_common (l1 l2: List Int) : List Int :=
  l1.filter (fun x => x ∈ l2)

-- LLM HELPER
def remove_duplicates (l: List Int) : List Int :=
  l.foldl (fun acc x => if x ∈ acc then acc else acc ++ [x]) []

-- LLM HELPER
def merge (l1 l2: List Int) : List Int :=
  match l1, l2 with
  | [], l2 => l2
  | l1, [] => l1
  | h1 :: t1, h2 :: t2 =>
    if h1 ≤ h2 then 
      h1 :: merge t1 l2
    else 
      h2 :: merge l1 t2
  termination_by l1.length + l2.length
  decreasing_by
    simp_wf
    · omega
    · omega

-- LLM HELPER
def merge_sort (l: List Int) : List Int :=
  if l.length ≤ 1 then l
  else
    let mid := l.length / 2
    let left := l.take mid
    let right := l.drop mid
    let sorted_left := merge_sort left
    let sorted_right := merge_sort right
    merge sorted_left sorted_right
  termination_by l.length

def implementation (l1 l2: List Int) : List Int :=
  let common := filter_common l1 l2
  let unique := remove_duplicates common
  merge_sort unique

-- LLM HELPER
lemma filter_common_spec (l1 l2: List Int) (x: Int) :
  x ∈ filter_common l1 l2 ↔ x ∈ l1 ∧ x ∈ l2 := by
  simp [filter_common, List.mem_filter]

-- LLM HELPER
lemma remove_duplicates_nodup (l: List Int) :
  (remove_duplicates l).Nodup := by
  simp [remove_duplicates]
  induction l with
  | nil => simp
  | cons h t ih =>
    simp [List.foldl_cons]
    by_cases h_mem : h ∈ List.foldl (fun acc x => if x ∈ acc then acc else acc ++ [x]) [] t
    · simp [h_mem]; exact ih
    · simp [h_mem]; exact List.nodup_append_of_nodup ih (List.nodup_singleton _) (fun _ h1 h2 => h_mem (List.mem_singleton.mp h2 ▸ h1))

-- LLM HELPER
lemma remove_duplicates_preserves_membership (l: List Int) (x: Int) :
  x ∈ remove_duplicates l ↔ x ∈ l := by
  simp [remove_duplicates]
  induction l with
  | nil => simp
  | cons h t ih =>
    simp [List.foldl_cons]
    by_cases h_mem : h ∈ List.foldl (fun acc x => if x ∈ acc then acc else acc ++ [x]) [] t
    · simp [h_mem]; exact ⟨fun h => Or.inr (ih.mp h), fun h => match h with | Or.inl rfl => ih.mpr (List.mem_of_mem_filter h_mem) | Or.inr h => ih.mpr h⟩
    · simp [h_mem, List.mem_append, List.mem_singleton]; exact ⟨fun h => match h with | Or.inl h => Or.inr (ih.mp h) | Or.inr rfl => Or.inl rfl, fun h => match h with | Or.inl rfl => Or.inr rfl | Or.inr h => Or.inl (ih.mpr h)⟩

-- LLM HELPER
lemma merge_preserves_membership (l1 l2: List Int) (x: Int) :
  x ∈ merge l1 l2 ↔ x ∈ l1 ∨ x ∈ l2 := by
  induction l1, l2 using merge.induct with
  | case1 l2 => simp [merge]
  | case2 l1 => simp [merge]
  | case3 h1 t1 h2 t2 =>
    simp [merge]
    by_cases h_le : h1 ≤ h2
    · simp [h_le]; exact ⟨fun h => match h with | Or.inl rfl => Or.inl (Or.inl rfl) | Or.inr h => match (this t1 (h2 :: t2)).mp h with | Or.inl h => Or.inl (Or.inr h) | Or.inr h => Or.inr h, fun h => match h with | Or.inl (Or.inl rfl) => Or.inl rfl | Or.inl (Or.inr h) => Or.inr ((this t1 (h2 :: t2)).mpr (Or.inl h)) | Or.inr h => Or.inr ((this t1 (h2 :: t2)).mpr (Or.inr h))⟩
    · simp [h_le]; exact ⟨fun h => match h with | Or.inl rfl => Or.inr (Or.inl rfl) | Or.inr h => match (this (h1 :: t1) t2).mp h with | Or.inl h => Or.inl h | Or.inr h => Or.inr (Or.inr h), fun h => match h with | Or.inl h => Or.inr ((this (h1 :: t1) t2).mpr (Or.inl h)) | Or.inr (Or.inl rfl) => Or.inl rfl | Or.inr (Or.inr h) => Or.inr ((this (h1 :: t1) t2).mpr (Or.inr h))⟩

-- LLM HELPER
lemma merge_sort_preserves_membership (l: List Int) (x: Int) :
  x ∈ merge_sort l ↔ x ∈ l := by
  induction l using List.strongInductionOn with
  | ind l ih =>
    simp [merge_sort]
    by_cases h : l.length ≤ 1
    · simp [h]
    · simp [h]
      have h1 : (List.take (l.length / 2) l).length < l.length := by simp [List.take_length]; omega
      have h2 : (List.drop (l.length / 2) l).length < l.length := by simp [List.drop_length]; omega
      rw [merge_preserves_membership, ih _ h1, ih _ h2]
      exact List.mem_append.symm.trans (List.mem_take_append_drop _ _).symm

-- LLM HELPER
lemma merge_sort_preserves_nodup (l: List Int) :
  l.Nodup → (merge_sort l).Nodup := by
  induction l using List.strongInductionOn with
  | ind l ih =>
    intro h_nodup
    simp [merge_sort]
    by_cases h : l.length ≤ 1
    · simp [h]; exact h_nodup
    · simp [h]
      have h1 : (List.take (l.length / 2) l).length < l.length := by simp [List.take_length]; omega
      have h2 : (List.drop (l.length / 2) l).length < l.length := by simp [List.drop_length]; omega
      have left_nodup := ih _ h1 (List.nodup_take _ h_nodup)
      have right_nodup := ih _ h2 (List.nodup_drop _ h_nodup)
      have disjoint : ∀ x, x ∈ merge_sort (List.take (l.length / 2) l) → x ∈ merge_sort (List.drop (l.length / 2) l) → False := by
        intro x hx1 hx2
        rw [merge_sort_preserves_membership] at hx1 hx2
        have : x ∈ List.take (l.length / 2) l ∧ x ∈ List.drop (l.length / 2) l := ⟨hx1, hx2⟩
        have : x ∈ l := List.mem_of_mem_take this.1
        have : x ∈ l := List.mem_of_mem_drop this.2
        have take_drop_disjoint : ∀ i, i < l.length / 2 → ∀ j, j ≥ l.length / 2 → j < l.length → i ≠ j := by
          intro i hi j hj1 hj2 hij
          omega
        have h_pos : 0 < l.length := by omega
        have h_mid : l.length / 2 < l.length := by omega
        exact List.nodup_iff_injective_get.mp h_nodup (List.get_of_mem hx1 h_pos) (List.get_of_mem hx2 h_pos) (take_drop_disjoint _ _ _ _ _)
      exact merge_preserves_nodup left_nodup right_nodup disjoint
  where
    merge_preserves_nodup : ∀ l1 l2, l1.Nodup → l2.Nodup → (∀ x, x ∈ l1 → x ∈ l2 → False) → (merge l1 l2).Nodup := by
      intro l1 l2
      induction l1, l2 using merge.induct with
      | case1 l2 => simp [merge]
      | case2 l1 => simp [merge]
      | case3 h1 t1 h2 t2 =>
        intro h_nodup1 h_nodup2 h_disj
        simp [merge]
        by_cases h_le : h1 ≤ h2
        · simp [h_le]
          constructor
          · intro h_mem
            rw [merge_preserves_membership] at h_mem
            cases h_mem with
            | inl h => exact List.nodup_cons.mp h_nodup1 |>.2 h
            | inr h => exact h_disj h1 (List.mem_cons_self _ _) h
          · exact this t1 (h2 :: t2) (List.nodup_cons.mp h_nodup1 |>.1) h_nodup2 (fun x hx1 hx2 => h_disj x (List.mem_cons_of_mem _ hx1) hx2)
        · simp [h_le]
          constructor
          · intro h_mem
            rw [merge_preserves_membership] at h_mem
            cases h_mem with
            | inl h => exact h_disj h2 h (List.mem_cons_self _ _)
            | inr h => exact List.nodup_cons.mp h_nodup2 |>.2 h
          · exact this (h1 :: t1) t2 h_nodup1 (List.nodup_cons.mp h_nodup2 |>.1) (fun x hx1 hx2 => h_disj x hx1 (List.mem_cons_of_mem _ hx2))

-- LLM HELPER
lemma merge_sort_sorted (l: List Int) : List.Sorted (· ≤ ·) (merge_sort l) := by
  induction l using List.strongInductionOn with
  | ind l ih =>
    simp [merge_sort]
    by_cases h : l.length ≤ 1
    · simp [h]
      cases l with
      | nil => exact List.sorted_nil
      | cons h t =>
        cases t with
        | nil => exact List.sorted_singleton _
        | cons => omega
    · simp [h]
      have h1 : (List.take (l.length / 2) l).length < l.length := by simp [List.take_length]; omega
      have h2 : (List.drop (l.length / 2) l).length < l.length := by simp [List.drop_length]; omega
      exact merge_sorted (ih _ h1) (ih _ h2)
  where
    merge_sorted : ∀ l1 l2, List.Sorted (· ≤ ·) l1 → List.Sorted (· ≤ ·) l2 → List.Sorted (· ≤ ·) (merge l1 l2) := by
      intro l1 l2
      induction l1, l2 using merge.induct with
      | case1 l2 => simp [merge]
      | case2 l1 => simp [merge]
      | case3 h1 t1 h2 t2 =>
        intro h_sorted1 h_sorted2
        simp [merge]
        by_cases h_le : h1 ≤ h2
        · simp [h_le]
          constructor
          · intro x hx
            rw [merge_preserves_membership] at hx
            cases hx with
            | inl hx => exact List.sorted_cons.mp h_sorted1 |>.2 _ hx
            | inr hx => exact le_trans h_le (List.sorted_cons.mp h_sorted2 |>.2 _ hx)
          · exact this t1 (h2 :: t2) (List.sorted_cons.mp h_sorted1 |>.1) h_sorted2
        · simp [h_le]
          constructor
          · intro x hx
            rw [merge_preserves_membership] at hx
            cases hx with
            | inl hx => exact le_trans (le_of_not_ge h_le) (List.sorted_cons.mp h_sorted1 |>.2 _ hx)
            | inr hx => exact List.sorted_cons.mp h_sorted2 |>.2 _ hx
          · exact this (h1 :: t1) t2 h_sorted1 (List.sorted_cons.mp h_sorted2 |>.1)

theorem correctness
(l1 l2: List Int)
: problem_spec implementation l1 l2 := by
  simp [problem_spec]
  use implementation l1 l2
  constructor
  · rfl
  · simp [implementation]
    constructor
    · -- is_unique
      intro i j hi hj hij
      simp [List.get_eq_getElem]
      have h_nodup := merge_sort_preserves_nodup (remove_duplicates (filter_common l1 l2)) (remove_duplicates_nodup _)
      exact List.nodup_iff_get_ne_get.mp h_nodup i j hi hj hij
    · constructor
      · -- is_sorted
        intro i hi
        simp [List.get_eq_getElem]
        have h_sorted := merge_sort_sorted (remove_duplicates (filter_common l1 l2))
        exact List.sorted_get_le_get h_sorted i (by omega) (by omega)
      · -- membership equivalence
        intro i
        simp [merge_sort_preserves_membership, remove_duplicates_preserves_membership, filter_common_spec]