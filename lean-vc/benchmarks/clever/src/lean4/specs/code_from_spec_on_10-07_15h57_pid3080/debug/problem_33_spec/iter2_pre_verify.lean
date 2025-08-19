import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(implementation: List Int → List Int)
-- inputs
(l: List Int) :=
-- spec
let spec (result: List Int) :=
  l.length = result.length ∧
  let every_third_idx := (List.range l.length).filter (λ i => i % 3 = 0);
  let every_third_val_in_result := every_third_idx.map (λ i => result.get! i);
  let every_third_val := every_third_idx.map (λ i => l.get! i);
  (∀ i, i < l.length → (i % 3 ≠ 0 → l.get! i = result.get! i)) ∧
  List.Sorted Int.le every_third_val_in_result ∧
  every_third_val.all (λ x => every_third_val_in_result.count x = every_third_val.count x);
-- program termination
∃ result, implementation l = result ∧
spec result

-- LLM HELPER
def get_indices_mod_3_eq_0 (n : Nat) : List Nat :=
  (List.range n).filter (λ i => i % 3 = 0)

-- LLM HELPER
def extract_elements_at_indices (l : List Int) (indices : List Nat) : List Int :=
  indices.map (λ i => l.get! i)

-- LLM HELPER
def replace_at_indices (l : List Int) (indices : List Nat) (new_vals : List Int) : List Int :=
  List.range l.length |>.map (λ i => 
    match indices.indexOf? i with
    | some idx => new_vals.get! idx
    | none => l.get! i)

-- LLM HELPER
def merge_sort (l : List Int) : List Int :=
  if l.length ≤ 1 then l
  else
    let mid := l.length / 2
    let left := l.take mid
    let right := l.drop mid
    merge (merge_sort left) (merge_sort right)
where
  merge (l1 l2 : List Int) : List Int :=
    match l1, l2 with
    | [], l2 => l2
    | l1, [] => l1
    | h1 :: t1, h2 :: t2 =>
      if h1 ≤ h2 then h1 :: merge t1 l2
      else h2 :: merge l1 t2

def implementation (l: List Int) : List Int := 
  if l.length = 0 then []
  else
    let every_third_idx := get_indices_mod_3_eq_0 l.length
    let every_third_val := extract_elements_at_indices l every_third_idx
    let sorted_every_third := merge_sort every_third_val
    replace_at_indices l every_third_idx sorted_every_third

-- LLM HELPER
lemma merge_sort_sorted (l : List Int) : List.Sorted Int.le (merge_sort l) := by
  induction l using List.strongRecOn with
  | ind l ih =>
    unfold merge_sort
    split_ifs with h
    · simp at h
      cases' l with hd tl
      · exact List.sorted_nil
      · cases' tl with hd2 tl2
        · exact List.sorted_singleton hd
        · simp at h
    · have h_len : l.length > 1 := by
        simp at h
        exact Nat.not_le.mp h
      let mid := l.length / 2
      let left := l.take mid
      let right := l.drop mid
      have h_left : left.length < l.length := by
        simp [List.length_take]
        exact Nat.min_lt_iff.mpr (Or.inl (Nat.div_lt_self (Nat.zero_lt_of_ne_zero (ne_of_gt h_len)) (by norm_num)))
      have h_right : right.length < l.length := by
        simp [List.length_drop]
        exact Nat.sub_lt (Nat.zero_lt_of_ne_zero (ne_of_gt h_len)) (Nat.zero_lt_of_ne_zero (ne_of_gt (Nat.div_pos (Nat.le_of_lt h_len) (by norm_num))))
      have ih_left := ih left h_left
      have ih_right := ih right h_right
      exact merge_preserves_sorted ih_left ih_right
where
  merge_preserves_sorted {l1 l2 : List Int} (h1 : List.Sorted Int.le l1) (h2 : List.Sorted Int.le l2) : 
    List.Sorted Int.le (merge_sort.merge l1 l2) := by
    induction l1, l2 using merge_sort.merge.induct with
    | case1 l2 => exact h2
    | case2 l1 => exact h1  
    | case3 h1 t1 h2 t2 =>
      simp [merge_sort.merge]
      split_ifs with h
      · apply List.Sorted.cons
        · exact List.Sorted.of_cons h1
        · cases' t1 with hd tl
          · simp [merge_sort.merge]
            split_ifs with h_cond
            · exact Int.le_of_lt (Int.lt_of_le_of_ne (Int.le_of_lt_or_eq h_cond) (Ne.symm (Int.ne_of_lt (Int.lt_of_le_of_ne h (Ne.symm (Int.ne_of_lt (Int.lt_of_le_of_ne h_cond (Ne.symm (Int.ne_of_lt (Int.lt_of_le_of_ne h (fun a => a.symm (Int.ne_of_lt (Int.lt_of_le_of_ne h_cond (fun a => a.symm))))))))))))
            · exact Int.le_refl h2
          · exact Int.le_refl h1
      · apply List.Sorted.cons
        · exact List.Sorted.of_cons h2
        · cases' t2 with hd tl
          · simp [merge_sort.merge]
            exact Int.le_of_not_le h
          · exact Int.le_refl h2

-- LLM HELPER
lemma merge_sort_count_eq (l : List Int) (x : Int) : (merge_sort l).count x = l.count x := by
  induction l using List.strongRecOn with
  | ind l ih =>
    unfold merge_sort
    split_ifs with h
    · rfl
    · let mid := l.length / 2
      let left := l.take mid
      let right := l.drop mid
      have h_left : left.length < l.length := by
        simp [List.length_take]
        exact Nat.min_lt_iff.mpr (Or.inl (Nat.div_lt_self (Nat.zero_lt_of_ne_zero (ne_of_gt (Nat.not_le.mp h))) (by norm_num)))
      have h_right : right.length < l.length := by
        simp [List.length_drop]
        exact Nat.sub_lt (Nat.zero_lt_of_ne_zero (ne_of_gt (Nat.not_le.mp h))) (Nat.zero_lt_of_ne_zero (ne_of_gt (Nat.div_pos (Nat.le_of_lt (Nat.not_le.mp h)) (by norm_num))))
      have ih_left := ih left h_left
      have ih_right := ih right h_right
      have h_split : l = left ++ right := by
        exact List.take_append_drop mid l
      rw [merge_count_eq, ih_left, ih_right, ← List.count_append, ← h_split]
where
  merge_count_eq (l1 l2 : List Int) (x : Int) : 
    (merge_sort.merge l1 l2).count x = l1.count x + l2.count x := by
    induction l1, l2 using merge_sort.merge.induct with
    | case1 l2 => simp [merge_sort.merge]
    | case2 l1 => simp [merge_sort.merge, Nat.add_zero]
    | case3 h1 t1 h2 t2 ih =>
      simp [merge_sort.merge]
      split_ifs with h
      · simp [List.count_cons]
        rw [ih]
        ring
      · simp [List.count_cons]
        rw [ih]
        ring

-- LLM HELPER
lemma replace_at_indices_length (l : List Int) (indices : List Nat) (new_vals : List Int) :
  (replace_at_indices l indices new_vals).length = l.length := by
  unfold replace_at_indices
  simp [List.length_map, List.length_range]

-- LLM HELPER
lemma replace_at_indices_preserves_non_indices (l : List Int) (indices : List Nat) (new_vals : List Int) (i : Nat) :
  i < l.length → i ∉ indices → (replace_at_indices l indices new_vals).get! i = l.get! i := by
  intro h_len h_not_in
  unfold replace_at_indices
  simp [List.get!_map, List.get!_range]
  rw [List.indexOf?_eq_none.mpr h_not_in]
  simp

theorem correctness
(l: List Int)
: problem_spec implementation l
:= by
  unfold problem_spec
  simp only [implementation]
  split_ifs with h
  · -- case l.length = 0
    simp [h]
    use []
    constructor
    · rfl
    · simp [h]
  · -- case l.length ≠ 0
    let every_third_idx := get_indices_mod_3_eq_0 l.length
    let every_third_val := extract_elements_at_indices l every_third_idx
    let sorted_every_third := merge_sort every_third_val
    let result := replace_at_indices l every_third_idx sorted_every_third
    
    use result
    constructor
    · rfl
    · constructor
      · exact replace_at_indices_length l every_third_idx sorted_every_third
      · constructor
        · intro i h_len h_not_mod3
          have h_not_in : i ∉ every_third_idx := by
            unfold get_indices_mod_3_eq_0
            simp [List.mem_filter]
            right
            exact h_not_mod3
          exact replace_at_indices_preserves_non_indices l every_third_idx sorted_every_third i h_len h_not_in
        · constructor
          · unfold get_indices_mod_3_eq_0 extract_elements_at_indices
            simp
            exact merge_sort_sorted every_third_val
          · unfold get_indices_mod_3_eq_0 extract_elements_at_indices
            simp [List.all_iff_forall]
            intro x
            exact merge_sort_count_eq every_third_val x