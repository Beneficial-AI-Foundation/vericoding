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
def merge_sort (l: List Int) : List Int :=
  if l.length ≤ 1 then l
  else
    let mid := l.length / 2
    let left := l.take mid
    let right := l.drop mid
    let sorted_left := merge_sort left
    let sorted_right := merge_sort right
    merge sorted_left sorted_right
where
  merge (l1 l2: List Int) : List Int :=
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
    all_goals simp_wf
    case h.1 => simp [Nat.add_assoc]; omega
    case h.2 => simp [Nat.add_assoc]; omega

def implementation (l1 l2: List Int) : List Int :=
  let common := filter_common l1 l2
  let unique := remove_duplicates common
  merge_sort unique

-- LLM HELPER
lemma filter_common_spec (l1 l2: List Int) (x: Int) :
  x ∈ filter_common l1 l2 ↔ x ∈ l1 ∧ x ∈ l2 := by
  simp [filter_common, List.mem_filter]

-- LLM HELPER
lemma remove_duplicates_unique (l: List Int) :
  let result := remove_duplicates l
  ∀ i j, i < result.length → j < result.length →
  i ≠ j → result[i]?.getD 0 ≠ result[j]?.getD 0 := by
  intro result i j hi hj hij
  simp [remove_duplicates] at result
  have h_nodup : result.Nodup := by
    simp [remove_duplicates]
    induction l with
    | nil => simp
    | cons h t ih =>
      simp [List.foldl_cons]
      by_cases h_mem : h ∈ List.foldl (fun acc x => if x ∈ acc then acc else acc ++ [x]) [] t
      · simp [h_mem]; exact ih
      · simp [h_mem]; exact List.nodup_append_of_nodup ih (List.nodup_singleton _) (fun _ h1 h2 => h_mem (List.mem_singleton.mp h2 ▸ h1))
  exact List.nodup_iff_get_ne_get.mp h_nodup i j hi hj hij

-- LLM HELPER
lemma remove_duplicates_preserves_membership (l: List Int) (x: Int) :
  x ∈ remove_duplicates l ↔ x ∈ l := by
  simp [remove_duplicates]
  induction l with
  | nil => simp
  | cons h t ih =>
    simp [List.foldl_cons]
    by_cases h_mem : h ∈ List.foldl (fun acc x => if x ∈ acc then acc else acc ++ [x]) [] t
    · simp [h_mem]
      constructor
      · intro h_x; exact Or.inr (ih.mp h_x)
      · intro h_x
        cases h_x with
        | inl h_eq => rw [h_eq]; exact ih.mpr (List.mem_of_mem_filter h_mem)
        | inr h_in => exact ih.mpr h_in
    · simp [h_mem]
      constructor
      · intro h_x
        simp [List.mem_append] at h_x
        cases h_x with
        | inl h_in => exact Or.inr (ih.mp h_in)
        | inr h_eq => simp [List.mem_singleton] at h_eq; exact Or.inl h_eq
      · intro h_x
        cases h_x with
        | inl h_eq => simp [List.mem_append, List.mem_singleton, h_eq]
        | inr h_in => simp [List.mem_append]; exact Or.inl (ih.mpr h_in)

-- LLM HELPER
lemma merge_sort_sorted (l: List Int) :
  let result := merge_sort l
  ∀ i, i < result.length - 1 →
  result[i]?.getD 0 ≤ result[i + 1]?.getD 0 := by
  intro result i hi
  simp [merge_sort] at result
  induction l using List.strongInductionOn with
  | ind l ih =>
    simp [merge_sort] at result
    by_cases h : l.length ≤ 1
    · simp [h] at result hi
      omega
    · simp [h] at result
      have merge_preserves_sorted : ∀ l1 l2, (∀ i, i < l1.length - 1 → l1[i]?.getD 0 ≤ l1[i + 1]?.getD 0) →
        (∀ i, i < l2.length - 1 → l2[i]?.getD 0 ≤ l2[i + 1]?.getD 0) →
        (∀ i, i < (merge_sort.merge l1 l2).length - 1 → (merge_sort.merge l1 l2)[i]?.getD 0 ≤ (merge_sort.merge l1 l2)[i + 1]?.getD 0) := by
        intro l1 l2 h1 h2 i hi_merge
        induction l1, l2 using merge_sort.merge.induct with
        | case1 l2 => simp [merge_sort.merge] at hi_merge ⊢; exact h2 i hi_merge
        | case2 l1 => simp [merge_sort.merge] at hi_merge ⊢; exact h1 i hi_merge
        | case3 h1 t1 h2 t2 =>
          simp [merge_sort.merge] at hi_merge ⊢
          by_cases h_le : h1 ≤ h2
          · simp [h_le] at hi_merge ⊢
            cases i with
            | zero => 
              by_cases h_empty : t1 = []
              · simp [h_empty] at hi_merge ⊢
                by_cases h_empty2 : t2 = []
                · simp [h_empty2] at hi_merge; omega
                · simp [h_empty2] at hi_merge ⊢
                  exact h_le
              · simp [h_empty] at hi_merge ⊢
                have : h1 ≤ (merge_sort.merge t1 (h2 :: t2))[0]?.getD 0 := by
                  cases t1 with
                  | nil => simp [merge_sort.merge]; exact h_le
                  | cons h3 t3 => 
                    simp [merge_sort.merge]
                    by_cases h_le2 : h3 ≤ h2
                    · simp [h_le2]
                      have : h1 ≤ h3 := by
                        have h1_sorted : ∀ i, i < (h1 :: t1).length - 1 → (h1 :: t1)[i]?.getD 0 ≤ (h1 :: t1)[i + 1]?.getD 0 := by
                          intro j hj
                          simp at hj ⊢
                          exact h1 j hj
                        exact h1_sorted 0 (by simp)
                      exact this
                    · simp [h_le2]; exact h_le
                exact this
            | succ j =>
              simp at hi_merge ⊢
              exact this (h1 :: t1) (h2 :: t2) (by simp [h1]) (by simp [h2]) j hi_merge
          · simp [h_le] at hi_merge ⊢
            have h_ge : h2 ≤ h1 := Nat.le_of_not_gt (fun h => h_le (le_of_lt h))
            cases i with
            | zero => 
              by_cases h_empty : t2 = []
              · simp [h_empty] at hi_merge ⊢
                by_cases h_empty1 : t1 = []
                · simp [h_empty1] at hi_merge; omega
                · simp [h_empty1] at hi_merge ⊢
                  exact h_ge
              · simp [h_empty] at hi_merge ⊢
                have : h2 ≤ (merge_sort.merge (h1 :: t1) t2)[0]?.getD 0 := by
                  cases t2 with
                  | nil => simp [merge_sort.merge]; exact h_ge
                  | cons h3 t3 => 
                    simp [merge_sort.merge]
                    by_cases h_le2 : h1 ≤ h3
                    · simp [h_le2]; exact h_ge
                    · simp [h_le2]
                      have : h2 ≤ h3 := by
                        have h2_sorted : ∀ i, i < (h2 :: t2).length - 1 → (h2 :: t2)[i]?.getD 0 ≤ (h2 :: t2)[i + 1]?.getD 0 := by
                          intro j hj
                          simp at hj ⊢
                          exact h2 j hj
                        exact h2_sorted 0 (by simp)
                      exact this
                exact this
            | succ j =>
              simp at hi_merge ⊢
              exact this (h1 :: t1) (h2 :: t2) (by simp [h1]) (by simp [h2]) j hi_merge
      apply merge_preserves_sorted
      · apply ih
        simp [List.take_length]; omega
      · apply ih
        simp [List.drop_length]; omega

-- LLM HELPER
lemma merge_sort_preserves_membership (l: List Int) (x: Int) :
  x ∈ merge_sort l ↔ x ∈ l := by
  induction l using List.strongInductionOn with
  | ind l ih =>
    simp [merge_sort]
    by_cases h : l.length ≤ 1
    · simp [h]
    · simp [h]
      have h1 : (List.take (l.length / 2) l).length < l.length := by
        simp [List.take_length]; omega
      have h2 : (List.drop (l.length / 2) l).length < l.length := by
        simp [List.drop_length]; omega
      have merge_preserves : ∀ l1 l2, x ∈ merge_sort.merge l1 l2 ↔ x ∈ l1 ∨ x ∈ l2 := by
        intro l1 l2
        induction l1, l2 using merge_sort.merge.induct with
        | case1 l2 => simp [merge_sort.merge]
        | case2 l1 => simp [merge_sort.merge]
        | case3 h1 t1 h2 t2 =>
          simp [merge_sort.merge]
          by_cases h_le : h1 ≤ h2
          · simp [h_le]
            constructor
            · intro h_mem
              cases h_mem with
              | inl h_eq => exact Or.inl (Or.inl h_eq)
              | inr h_in => 
                have := this t1 (h2 :: t2)
                rw [this] at h_in
                cases h_in with
                | inl h_t1 => exact Or.inl (Or.inr h_t1)
                | inr h_h2t2 => exact Or.inr h_h2t2
            · intro h_mem
              cases h_mem with
              | inl h_l1 =>
                cases h_l1 with
                | inl h_eq => exact Or.inl h_eq
                | inr h_t1 => 
                  have := this t1 (h2 :: t2)
                  rw [this]
                  exact Or.inr (Or.inl h_t1)
              | inr h_l2 =>
                have := this t1 (h2 :: t2)
                rw [this]
                exact Or.inr (Or.inr h_l2)
          · simp [h_le]
            constructor
            · intro h_mem
              cases h_mem with
              | inl h_eq => exact Or.inr (Or.inl h_eq)
              | inr h_in => 
                have := this (h1 :: t1) t2
                rw [this] at h_in
                cases h_in with
                | inl h_h1t1 => exact Or.inl h_h1t1
                | inr h_t2 => exact Or.inr (Or.inr h_t2)
            · intro h_mem
              cases h_mem with
              | inl h_l1 =>
                have := this (h1 :: t1) t2
                rw [this]
                exact Or.inr (Or.inl h_l1)
              | inr h_l2 =>
                cases h_l2 with
                | inl h_eq => exact Or.inl h_eq
                | inr h_t2 => 
                  have := this (h1 :: t1) t2
                  rw [this]
                  exact Or.inr (Or.inr h_t2)
      rw [merge_preserves, ih _ h1, ih _ h2]
      exact List.mem_append.symm.trans (List.mem_take_append_drop _ _).symm

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
      apply remove_duplicates_unique
    · constructor
      · -- is_sorted
        apply merge_sort_sorted
      · -- membership equivalence
        intro i
        simp [merge_sort_preserves_membership, remove_duplicates_preserves_membership, filter_common_spec]