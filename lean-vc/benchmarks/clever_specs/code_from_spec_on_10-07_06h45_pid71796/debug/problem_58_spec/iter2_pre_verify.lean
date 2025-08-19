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
        simp [left]
        exact List.length_take_lt_length_of_pos (by simp [mid]; norm_num) (by simp; norm_num)
      have h2 : right.length < (y::z::rest).length := by
        simp [right]
        exact List.length_drop_lt_length_of_pos (by simp [mid]; norm_num) (by simp; norm_num)
      rw [ih left h1, ih right h2]
      simp [merge_mem]
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
          exact ⟨Nat.le_sub_of_add_le (by simp [mid]; exact Nat.le_of_not_gt h_lt), h.1⟩
where
  merge_mem (l1 l2: List Int) (x: Int) : x ∈ merge_sort.merge l1 l2 ↔ x ∈ l1 ∨ x ∈ l2 := by
    induction l1, l2 using merge_sort.merge.induct with
    | case1 l2 => simp [merge_sort.merge]
    | case2 l1 => simp [merge_sort.merge]
    | case3 x xs y ys h_le ih => 
      simp [merge_sort.merge, h_le]
      rw [ih]
      simp [List.mem_cons_iff]
      tauto
    | case4 x xs y ys h_not_le ih =>
      simp [merge_sort.merge, h_not_le]
      rw [ih]
      simp [List.mem_cons_iff]
      tauto

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
        simp [left]
        exact List.length_take_lt_length_of_pos (by simp [mid]; norm_num) (by simp; norm_num)
      have h2 : right.length < (x::y::rest).length := by
        simp [right]
        exact List.length_drop_lt_length_of_pos (by simp [mid]; norm_num) (by simp; norm_num)
      exact merge_sorted (merge_sort left) (merge_sort right) (ih left h1) (ih right h2)
where
  merge_sorted (l1 l2: List Int) 
    (h1: ∀ i, i < l1.length - 1 → l1[i]! ≤ l1[i + 1]!)
    (h2: ∀ i, i < l2.length - 1 → l2[i]! ≤ l2[i + 1]!) :
    ∀ i, i < (merge_sort.merge l1 l2).length - 1 → (merge_sort.merge l1 l2)[i]! ≤ (merge_sort.merge l1 l2)[i + 1]! := by
    induction l1, l2 using merge_sort.merge.induct with
    | case1 l2 => simp [merge_sort.merge]; exact h2
    | case2 l1 => simp [merge_sort.merge]; exact h1
    | case3 x xs y ys h_le ih => 
      simp [merge_sort.merge, h_le]
      intro i hi
      cases i with
      | zero => 
        simp
        cases merge_sort.merge xs (y::ys) with
        | nil => simp
        | cons z zs => 
          simp
          have : z ∈ merge_sort.merge xs (y::ys) := by simp
          rw [← merge_sort.merge_mem] at this
          cases this with
          | inl h => 
            have : z ∈ xs := h
            if h_empty : xs = [] then
              simp [h_empty, merge_sort.merge] at this
            else
              have : x ≤ z := by
                cases xs with
                | nil => contradiction
                | cons w ws =>
                  have : x ≤ w := by
                    have : 0 < (x::w::ws).length - 1 := by simp; norm_num
                    exact h1 0 this
                  have : z = w ∨ z ∈ ws := by simp [List.mem_cons_iff] at h; exact h
                  cases this with
                  | inl h => rw [h]; exact this
                  | inr h => 
                    have : w ≤ z := by
                      have h_sorted : ∀ i, i < (w::ws).length - 1 → (w::ws)[i]! ≤ (w::ws)[i + 1]! := by
                        intro i hi
                        exact h1 (i + 1) (by simp; exact Nat.succ_lt_succ hi)
                      exact list_sorted_implies_le (w::ws) h_sorted z h
                    exact le_trans this this
              exact this
          | inr h => 
            have : z ∈ y::ys := h
            exact le_trans h_le (by 
              cases this with
              | inl h => rw [h]; le_refl
              | inr h => 
                have : y ≤ z := by
                  have h_sorted : ∀ i, i < (y::ys).length - 1 → (y::ys)[i]! ≤ (y::ys)[i + 1]! := h2
                  exact list_sorted_implies_le (y::ys) h_sorted z h
                exact this)
      | succ j =>
        simp
        exact ih (by 
          intro i hi
          exact h1 (i + 1) (by simp; exact Nat.succ_lt_succ hi)) h2 j (by simp at hi; exact hi)
    | case4 x xs y ys h_not_le ih =>
      simp [merge_sort.merge, h_not_le]
      intro i hi
      cases i with
      | zero => 
        simp
        cases merge_sort.merge (x::xs) ys with
        | nil => simp
        | cons z zs => 
          simp
          have : z ∈ merge_sort.merge (x::xs) ys := by simp
          rw [← merge_sort.merge_mem] at this
          cases this with
          | inl h => 
            have : z ∈ x::xs := h
            have : ¬x ≤ y := h_not_le
            have : y < x := Int.lt_of_not_le this
            have : y ≤ z := by
              cases h with
              | inl h => rw [h]; exact le_of_lt this
              | inr h => 
                have : x ≤ z := by
                  have h_sorted : ∀ i, i < (x::xs).length - 1 → (x::xs)[i]! ≤ (x::xs)[i + 1]! := h1
                  exact list_sorted_implies_le (x::xs) h_sorted z h
                exact le_trans (le_of_lt this) this
            exact this
          | inr h => 
            have : z ∈ ys := h
            have : y ≤ z := by
              have h_sorted : ∀ i, i < (y::ys).length - 1 → (y::ys)[i]! ≤ (y::ys)[i + 1]! := h2
              have : y ∈ y::ys := by simp
              exact list_sorted_implies_le (y::ys) h_sorted z h
            exact this
      | succ j =>
        simp
        exact ih h1 (by 
          intro i hi
          exact h2 (i + 1) (by simp; exact Nat.succ_lt_succ hi)) j (by simp at hi; exact hi)

-- LLM HELPER
lemma list_sorted_implies_le (l: List Int) (h: ∀ i, i < l.length - 1 → l[i]! ≤ l[i + 1]!) (x: Int) (hx: x ∈ l) : 
  ∀ y ∈ l, ∃ i j, i < l.length ∧ j < l.length ∧ l[i]! = x ∧ l[j]! = y ∧ (i ≤ j → x ≤ y) := by
  intro y hy
  have ⟨i, hi, hxi⟩ : ∃ i, i < l.length ∧ l[i]! = x := List.mem_iff_get.mp hx
  have ⟨j, hj, hyj⟩ : ∃ j, j < l.length ∧ l[j]! = y := List.mem_iff_get.mp hy
  use i, j, hi, hj, hxi, hyj
  intro hij
  rw [← hxi, ← hyj]
  exact sorted_list_indices_le l h i j hi hj hij
where
  sorted_list_indices_le (l: List Int) (h: ∀ i, i < l.length - 1 → l[i]! ≤ l[i + 1]!) 
    (i j: Nat) (hi: i < l.length) (hj: j < l.length) (hij: i ≤ j) : l[i]! ≤ l[j]! := by
    induction hij using Nat.le_induction with
    | refl => le_refl
    | succ k hik ih =>
      have hk : k < l.length := Nat.lt_of_succ_le (Nat.succ_le_of_lt hj)
      have hkj : k < l.length - 1 := by
        have : k + 1 < l.length := hj
        exact Nat.lt_sub_of_add_lt this
      exact le_trans ih (h k hkj)

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
lemma remove_duplicates_preserves_sorted (l: List Int) : 
  (∀ i, i < l.length - 1 → l[i]! ≤ l[i + 1]!) →
  (∀ i, i < (remove_duplicates l).length - 1 → (remove_duplicates l)[i]! ≤ (remove_duplicates l)[i + 1]!) := by
  induction l with
  | nil => simp [remove_duplicates]
  | cons x xs ih =>
    intro h
    simp [remove_duplicates]
    split_ifs with hmem
    · apply ih
      intro i hi
      exact h (i + 1) (by simp; exact Nat.succ_lt_succ hi)
    · intro i hi
      cases i with
      | zero =>
        simp
        have : (remove_duplicates xs)[0]! ∈ remove_duplicates xs := by
          exact List.get_mem _ 0 (by simp at hi; exact Nat.pos_of_ne_zero (Nat.ne_of_gt hi))
        rw [remove_duplicates_mem] at this
        have h_sorted : ∀ i, i < xs.length - 1 → xs[i]! ≤ xs[i + 1]! := by
          intro i hi
          exact h (i + 1) (by simp; exact Nat.succ_lt_succ hi)
        have : x ∈ x::xs := by simp
        have : (remove_duplicates xs)[0]! ∈ x::xs := by simp; exact this
        cases this with
        | inl heq => 
          rw [heq]
          le_refl
        | inr hmem_xs =>
          have : x ≤ (remove_duplicates xs)[0]! := by
            have : x ∈ xs → x ≤ xs[0]! := by
              intro hx
              cases xs with
              | nil => contradiction
              | cons y ys =>
                have : x ≤ y := h 0 (by simp; norm_num)
                have : y = xs[0]! := by simp
                rw [← this]
                exact this
            exact this hmem_xs
          exact this
      | succ k =>
        simp
        have h_sorted : ∀ i, i < xs.length - 1 → xs[i]! ≤ xs[i + 1]! := by
          intro i hi_xs
          exact h (i + 1) (by simp; exact Nat.succ_lt_succ hi_xs)
        exact ih h_sorted k (by simp at hi; exact hi)

theorem correctness
(l1 l2: List Int)
: problem_spec implementation l1 l2
:= by
  simp [problem_spec, implementation]
  use remove_duplicates (merge_sort (intersection l1 l2))
  constructor
  · rfl
  · constructor
    · -- is_unique
      exact remove_duplicates_unique (merge_sort (intersection l1 l2))
    · constructor
      · -- is_sorted
        apply remove_duplicates_preserves_sorted
        exact merge_sort_sorted (intersection l1 l2)
      · -- membership equivalence
        intro i
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