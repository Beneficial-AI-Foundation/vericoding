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
def intersection (l1 l2: List Int) : List Int :=
  l1.filter (fun x => x ∈ l2)

-- LLM HELPER
def merge_sort (l: List Int) : List Int :=
  match l with
  | [] => []
  | [x] => [x]
  | _ => 
    let mid := l.length / 2
    let left := l.take mid
    let right := l.drop mid
    let sorted_left := merge_sort left
    let sorted_right := merge_sort right
    merge sorted_left sorted_right
  termination_by l.length
  decreasing_by
    · simp only [List.length_take]
      omega
    · simp only [List.length_drop]
      omega
where
  merge (l1 l2: List Int) : List Int :=
    match l1, l2 with
    | [], l2 => l2
    | l1, [] => l1
    | x::xs, y::ys => 
      if x ≤ y then x :: merge xs (y::ys)
      else y :: merge (x::xs) ys

-- LLM HELPER
def remove_duplicates (l: List Int) : List Int :=
  match l with
  | [] => []
  | x::xs => 
    let rest := remove_duplicates xs
    if x ∈ rest then rest
    else x :: rest

def implementation (l1 l2: List Int) : List Int := 
  remove_duplicates (merge_sort (intersection l1 l2))

-- LLM HELPER
lemma intersection_mem (l1 l2: List Int) (x: Int) : x ∈ intersection l1 l2 ↔ x ∈ l1 ∧ x ∈ l2 := by
  simp [intersection, List.mem_filter]

-- LLM HELPER
lemma merge_mem (l1 l2: List Int) (x: Int) : x ∈ merge_sort.merge l1 l2 ↔ x ∈ l1 ∨ x ∈ l2 := by
  induction l1, l2 using merge_sort.merge.induct with
  | case1 l2 => simp [merge_sort.merge]
  | case2 l1 => simp [merge_sort.merge]
  | case3 x xs y ys h_le ih => 
    simp [merge_sort.merge, h_le]
    rw [ih]
    simp [List.mem_cons_iff]
    constructor
    · intro h
      cases h with
      | inl h => left; left; exact h
      | inr h => 
        cases h with
        | inl h => left; right; exact h
        | inr h => right; exact h
    · intro h
      cases h with
      | inl h => 
        cases h with
        | inl h => left; exact h
        | inr h => right; left; exact h
      | inr h => right; right; exact h
  | case4 x xs y ys h_not_le ih =>
    simp [merge_sort.merge, h_not_le]
    rw [ih]
    simp [List.mem_cons_iff]
    constructor
    · intro h
      cases h with
      | inl h => right; left; exact h
      | inr h => 
        cases h with
        | inl h => left; exact h
        | inr h => right; right; exact h
    · intro h
      cases h with
      | inl h => right; left; exact h
      | inr h => 
        cases h with
        | inl h => left; exact h
        | inr h => right; right; exact h

-- LLM HELPER
lemma merge_sort_mem (l: List Int) (x: Int) : x ∈ merge_sort l ↔ x ∈ l := by
  induction l using List.strongInductionOn with
  | ind l ih =>
    match l with
    | [] => simp [merge_sort]
    | [y] => simp [merge_sort]
    | y::z::rest =>
      simp [merge_sort]
      let mid := (y::z::rest).length / 2
      let left := (y::z::rest).take mid
      let right := (y::z::rest).drop mid
      have h1 : left.length < (y::z::rest).length := by
        simp [left, List.length_take]
        omega
      have h2 : right.length < (y::z::rest).length := by
        simp [right, List.length_drop]
        omega
      rw [ih left h1, ih right h2]
      rw [merge_mem]
      simp [List.mem_take, List.mem_drop]
      constructor
      · intro h
        cases h with
        | inl h => exact ⟨h.1, Nat.le_add_right _ _⟩
        | inr h => exact ⟨h.2, Nat.le_add_left _ _⟩
      · intro h
        if h_lt : h.2 < mid then
          left
          exact ⟨h.1, h_lt⟩
        else
          right
          exact ⟨Nat.le_sub_of_add_le (by simp; exact Nat.le_of_not_gt h_lt), h.1⟩

-- LLM HELPER
lemma remove_duplicates_mem (l: List Int) (x: Int) : x ∈ remove_duplicates l ↔ x ∈ l := by
  induction l with
  | nil => simp [remove_duplicates]
  | cons y ys ih =>
    simp [remove_duplicates]
    split_ifs with h
    · rw [ih]
      simp [List.mem_cons_iff]
      constructor
      · intro hx
        right
        exact hx
      · intro hx
        cases hx with
        | inl hxy => rw [hxy]; exact h
        | inr hx => exact hx
    · simp [List.mem_cons_iff]
      rw [ih]
      simp [List.mem_cons_iff]

-- LLM HELPER
lemma remove_duplicates_unique (l: List Int) : 
  ∀ i j, i < (remove_duplicates l).length → j < (remove_duplicates l).length →
  i ≠ j → (remove_duplicates l)[i]! ≠ (remove_duplicates l)[j]! := by
  induction l with
  | nil => simp [remove_duplicates]
  | cons x xs ih =>
    simp [remove_duplicates]
    split_ifs with h
    · exact ih
    · intro i j hi hj hij
      cases i with
      | zero =>
        cases j with
        | zero => contradiction
        | succ k =>
          simp
          have : (remove_duplicates xs)[k]! ∈ remove_duplicates xs := by
            exact List.get_mem _ k (by simp at hj; exact hj)
          rw [remove_duplicates_mem] at this
          intro hcontra
          rw [hcontra] at this
          exact h this
      | succ i' =>
        cases j with
        | zero =>
          simp
          have : (remove_duplicates xs)[i']! ∈ remove_duplicates xs := by
            exact List.get_mem _ i' (by simp at hi; exact hi)
          rw [remove_duplicates_mem] at this
          intro hcontra
          rw [← hcontra] at this
          exact h this
        | succ j' =>
          simp
          exact ih i' j' (by simp at hi; exact hi) (by simp at hj; exact hj) (by simp at hij; exact hij)

-- LLM HELPER
lemma merge_sorted (l1 l2: List Int) : 
  (∀ i, i < l1.length - 1 → l1[i]! ≤ l1[i + 1]!) →
  (∀ i, i < l2.length - 1 → l2[i]! ≤ l2[i + 1]!) →
  (∀ i, i < (merge_sort.merge l1 l2).length - 1 → (merge_sort.merge l1 l2)[i]! ≤ (merge_sort.merge l1 l2)[i + 1]!) := by
  induction l1, l2 using merge_sort.merge.induct with
  | case1 l2 => simp [merge_sort.merge]
  | case2 l1 => simp [merge_sort.merge]
  | case3 x xs y ys h_le ih => 
    simp [merge_sort.merge, h_le]
    intro h1 h2 i hi
    cases i with
    | zero =>
      simp
      if h : xs.length = 0 then
        simp [h]
        cases ys with
        | nil => simp
        | cons z zs => simp; exact h_le
      else
        have : (merge_sort.merge xs (y::ys))[0]! ∈ merge_sort.merge xs (y::ys) := by
          exact List.get_mem _ 0 (by simp at hi; simp; omega)
        rw [merge_mem] at this
        cases this with
        | inl this => 
          have : xs[0]! ≤ x := by
            exact h1 0 (by simp; omega)
          exact le_trans h_le this
        | inr this => exact h_le
    | succ i' =>
      simp
      exact ih (by simp at h1; exact h1) h2 i' (by simp at hi; exact hi)
  | case4 x xs y ys h_not_le ih =>
    simp [merge_sort.merge, h_not_le]
    intro h1 h2 i hi
    cases i with
    | zero =>
      simp
      if h : ys.length = 0 then
        simp [h]
        cases xs with
        | nil => simp
        | cons z zs => simp; exact Int.le_of_not_gt h_not_le
      else
        have : (merge_sort.merge (x::xs) ys)[0]! ∈ merge_sort.merge (x::xs) ys := by
          exact List.get_mem _ 0 (by simp at hi; simp; omega)
        rw [merge_mem] at this
        cases this with
        | inl this => exact Int.le_of_not_gt h_not_le
        | inr this => 
          have : ys[0]! ≤ y := by
            exact h2 0 (by simp; omega)
          exact le_trans (Int.le_of_not_gt h_not_le) this
    | succ i' =>
      simp
      exact ih h1 (by simp at h2; exact h2) i' (by simp at hi; exact hi)

-- LLM HELPER
lemma merge_sort_sorted (l: List Int) : 
  ∀ i, i < (merge_sort l).length - 1 → (merge_sort l)[i]! ≤ (merge_sort l)[i + 1]! := by
  induction l using List.strongInductionOn with
  | ind l ih =>
    match l with
    | [] => simp [merge_sort]
    | [x] => simp [merge_sort]
    | x::y::rest =>
      simp [merge_sort]
      let mid := (x::y::rest).length / 2
      let left := (x::y::rest).take mid
      let right := (x::y::rest).drop mid
      have h1 : left.length < (x::y::rest).length := by
        simp [left, List.length_take]
        omega
      have h2 : right.length < (x::y::rest).length := by
        simp [right, List.length_drop]
        omega
      exact merge_sorted (merge_sort left) (merge_sort right) (ih left h1) (ih right h2)

-- LLM HELPER
lemma remove_duplicates_sorted (l: List Int) : 
  (∀ i, i < l.length - 1 → l[i]! ≤ l[i + 1]!) →
  (∀ i, i < (remove_duplicates l).length - 1 → (remove_duplicates l)[i]! ≤ (remove_duplicates l)[i + 1]!) := by
  induction l with
  | nil => simp [remove_duplicates]
  | cons x xs ih =>
    simp [remove_duplicates]
    split_ifs with h
    · intro h_sorted
      exact ih (by simp at h_sorted; exact h_sorted)
    · intro h_sorted i hi
      cases i with
      | zero =>
        simp
        if h_empty : remove_duplicates xs = [] then
          simp [h_empty] at hi
        else
          have : (remove_duplicates xs)[0]! ∈ remove_duplicates xs := by
            exact List.get_mem _ 0 (by simp [h_empty]; omega)
          rw [remove_duplicates_mem] at this
          cases xs with
          | nil => simp [remove_duplicates] at h_empty
          | cons y ys =>
            simp at h_sorted
            exact h_sorted.1
      | succ i' =>
        simp
        exact ih (by simp at h_sorted; exact h_sorted.2) i' (by simp at hi; exact hi)

theorem correctness (l1 l2: List Int) : problem_spec implementation l1 l2 := by
  simp [problem_spec, implementation]
  use remove_duplicates (merge_sort (intersection l1 l2))
  constructor
  · rfl
  · constructor
    · exact remove_duplicates_unique (merge_sort (intersection l1 l2))
    · constructor
      · exact remove_duplicates_sorted (merge_sort (intersection l1 l2)) (merge_sort_sorted (intersection l1 l2))
      · intro i
        constructor
        · intro h
          rw [remove_duplicates_mem] at h
          rw [merge_sort_mem] at h
          rw [intersection_mem] at h
          exact h
        · intro h
          rw [remove_duplicates_mem]
          rw [merge_sort_mem]
          rw [intersection_mem]
          exact h