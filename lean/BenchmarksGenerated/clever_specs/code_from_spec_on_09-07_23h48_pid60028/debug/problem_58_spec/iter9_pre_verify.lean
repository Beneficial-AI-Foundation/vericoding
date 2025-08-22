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
    simp [List.length_cons]
    omega

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
  decreasing_by
    simp_wf
    simp [List.length_take, List.length_drop]
    omega

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
    · simp [h_mem]; exact ⟨fun h => Or.inr (ih.mp h), fun h => match h with | Or.inl rfl => ih.mpr h_mem | Or.inr h => ih.mpr h⟩
    · simp [h_mem, List.mem_append, List.mem_singleton]; exact ⟨fun h => match h with | Or.inl h => Or.inr (ih.mp h) | Or.inr rfl => Or.inl rfl, fun h => match h with | Or.inl rfl => Or.inr rfl | Or.inr h => Or.inl (ih.mpr h)⟩

-- LLM HELPER
lemma merge_preserves_membership (l1 l2: List Int) (x: Int) :
  x ∈ merge l1 l2 ↔ x ∈ l1 ∨ x ∈ l2 := by
  induction l1, l2 using merge.induct with
  | case1 l2 => simp [merge]
  | case2 l1 => simp [merge]
  | case3 h1 t1 h2 t2 ih =>
    simp [merge]
    by_cases h_le : h1 ≤ h2
    · simp [h_le]; simp [ih]
    · simp [h_le]; simp [ih]

-- LLM HELPER
lemma merge_sort_preserves_membership (l: List Int) (x: Int) :
  x ∈ merge_sort l ↔ x ∈ l := by
  induction l using List.strongInductionOn with
  | ind l ih =>
    simp [merge_sort]
    by_cases h : l.length ≤ 1
    · simp [h]
    · simp [h]
      rw [merge_preserves_membership]
      constructor
      · intro h_mem
        cases h_mem with
        | inl h => exact List.mem_of_mem_take h
        | inr h => exact List.mem_of_mem_drop h
      · intro h_mem
        cases List.mem_take_append_drop (l.length / 2) l |>.mp h_mem with
        | inl h => exact Or.inl h
        | inr h => exact Or.inr h

-- LLM HELPER
lemma merge_sorted (l1 l2: List Int) :
  List.Sorted (· ≤ ·) l1 → List.Sorted (· ≤ ·) l2 → List.Sorted (· ≤ ·) (merge l1 l2) := by
  intro h_sorted1 h_sorted2
  induction l1, l2 using merge.induct with
  | case1 l2 => simp [merge, h_sorted2]
  | case2 l1 => simp [merge, h_sorted1]
  | case3 h1 t1 h2 t2 ih =>
    simp [merge]
    by_cases h_le : h1 ≤ h2
    · simp [h_le]
      constructor
      · intro x hx
        rw [merge_preserves_membership] at hx
        cases hx with
        | inl hx => exact List.sorted_cons.mp h_sorted1 |>.2 _ hx
        | inr hx => exact le_trans h_le (List.sorted_cons.mp h_sorted2 |>.2 _ hx)
      · exact ih (List.sorted_cons.mp h_sorted1 |>.1) h_sorted2
    · simp [h_le]
      constructor
      · intro x hx
        rw [merge_preserves_membership] at hx
        cases hx with
        | inl hx => exact le_trans (le_of_not_ge h_le) (List.sorted_cons.mp h_sorted1 |>.2 _ hx)
        | inr hx => exact List.sorted_cons.mp h_sorted2 |>.2 _ hx
      · exact ih h_sorted1 (List.sorted_cons.mp h_sorted2 |>.1)

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
      have h1 : (List.take (l.length / 2) l).length < l.length := by simp [List.length_take]; omega
      have h2 : (List.drop (l.length / 2) l).length < l.length := by simp [List.length_drop]; omega
      exact merge_sorted (merge_sort (List.take (l.length / 2) l)) (merge_sort (List.drop (l.length / 2) l)) (ih _ h1) (ih _ h2)

-- LLM HELPER
lemma merge_nodup (l1 l2: List Int) :
  l1.Nodup → l2.Nodup → (∀ x, x ∈ l1 → x ∉ l2) → (merge l1 l2).Nodup := by
  intro h_nodup1 h_nodup2 h_disj
  induction l1, l2 using merge.induct with
  | case1 l2 => simp [merge, h_nodup2]
  | case2 l1 => simp [merge, h_nodup1]
  | case3 h1 t1 h2 t2 ih =>
    simp [merge]
    by_cases h_le : h1 ≤ h2
    · simp [h_le]
      constructor
      · intro h_mem
        rw [merge_preserves_membership] at h_mem
        cases h_mem with
        | inl h => exact List.nodup_cons.mp h_nodup1 |>.2 h
        | inr h => exact h_disj h1 (List.mem_cons_self _ _) h
      · exact ih (List.nodup_cons.mp h_nodup1 |>.1) h_nodup2 (fun x hx => h_disj x (List.mem_cons_of_mem _ hx))
    · simp [h_le]
      constructor
      · intro h_mem
        rw [merge_preserves_membership] at h_mem
        cases h_mem with
        | inl h => exact h_disj h2 h (List.mem_cons_self _ _)
        | inr h => exact List.nodup_cons.mp h_nodup2 |>.2 h
      · exact ih h_nodup1 (List.nodup_cons.mp h_nodup2 |>.1) (fun x hx => h_disj x hx)

-- LLM HELPER
lemma merge_sort_nodup (l: List Int) : l.Nodup → (merge_sort l).Nodup := by
  intro h_nodup
  induction l using List.strongInductionOn with
  | ind l ih =>
    simp [merge_sort]
    by_cases h : l.length ≤ 1
    · simp [h, h_nodup]
    · simp [h]
      have h1 : (List.take (l.length / 2) l).length < l.length := by simp [List.length_take]; omega
      have h2 : (List.drop (l.length / 2) l).length < l.length := by simp [List.length_drop]; omega
      have left_nodup := ih _ h1 (List.nodup_take _ h_nodup)
      have right_nodup := ih _ h2 (List.nodup_drop _ h_nodup)
      apply merge_nodup
      · exact left_nodup
      · exact right_nodup
      · intro x hx_left hx_right
        rw [merge_sort_preserves_membership] at hx_left hx_right
        have hx_take : x ∈ l.take (l.length / 2) := hx_left
        have hx_drop : x ∈ l.drop (l.length / 2) := hx_right
        have hx_pos : x ∈ l := List.mem_of_mem_take hx_take
        have hx_pos2 : x ∈ l := List.mem_of_mem_drop hx_drop
        have : ∃ i, i < l.length ∧ l[i]! = x := by
          have hx_idx := List.mem_iff_get.mp hx_pos
          obtain ⟨i, hi, hval⟩ := hx_idx
          exact ⟨i, hi, hval⟩
        obtain ⟨i, hi, hval⟩ := this
        have : ∃ j, j < l.length ∧ l[j]! = x := by
          have hx_idx := List.mem_iff_get.mp hx_pos2
          obtain ⟨j, hj, hval2⟩ := hx_idx
          exact ⟨j, hj, hval2⟩
        obtain ⟨j, hj, hval2⟩ := this
        have : i = j := by
          rw [← hval, ← hval2]
          exact List.nodup_iff_get_ne_get.mp h_nodup i j hi hj (fun h => by rw [h] at hval; rw [hval] at hval2; exact hval2)
        have i_lt_mid : i < l.length / 2 := by
          have : l[i]! ∈ l.take (l.length / 2) := by rw [hval]; exact hx_take
          exact List.mem_take.mp this
        have j_ge_mid : j ≥ l.length / 2 := by
          have : l[j]! ∈ l.drop (l.length / 2) := by rw [hval2]; exact hx_drop
          exact List.mem_drop.mp this
        rw [this] at i_lt_mid
        omega

-- LLM HELPER
lemma nodup_get_ne_get (l: List Int) (i j: Nat) (hi: i < l.length) (hj: j < l.length) (hij: i ≠ j) :
  l.Nodup → l[i]! ≠ l[j]! := by
  intro h_nodup
  exact List.nodup_iff_get_ne_get.mp h_nodup i j hi hj hij

-- LLM HELPER
lemma sorted_get_le_get (l: List Int) (i: Nat) (hi: i < l.length - 1) :
  List.Sorted (· ≤ ·) l → l[i]! ≤ l[i + 1]! := by
  intro h_sorted
  have hi_succ : i + 1 < l.length := by omega
  exact List.sorted_get_le_get h_sorted i hi_succ (by omega)

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
      have h_nodup := merge_sort_nodup (remove_duplicates (filter_common l1 l2)) (remove_duplicates_nodup _)
      exact nodup_get_ne_get (merge_sort (remove_duplicates (filter_common l1 l2))) i j hi hj hij h_nodup
    · constructor
      · -- is_sorted
        intro i hi
        have h_sorted := merge_sort_sorted (remove_duplicates (filter_common l1 l2))
        exact sorted_get_le_get (merge_sort (remove_duplicates (filter_common l1 l2))) i hi h_sorted
      · -- membership equivalence
        intro i
        simp [merge_sort_preserves_membership, remove_duplicates_preserves_membership, filter_common_spec]