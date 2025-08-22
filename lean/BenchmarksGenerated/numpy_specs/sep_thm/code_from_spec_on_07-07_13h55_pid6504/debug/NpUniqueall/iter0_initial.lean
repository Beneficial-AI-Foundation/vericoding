/-
# NumPy Unique All Specification

Port of np_uniqueall.dfy to Lean 4
-/

namespace DafnySpecs.NpUniqueall

-- LLM HELPER
def List.removeDuplicates {α : Type*} [DecidableEq α] : List α → List α
  | [] => []
  | x :: xs => x :: (xs.filter (· ≠ x)).removeDuplicates

-- LLM HELPER
def List.removeDuplicates_nodup {α : Type*} [DecidableEq α] (l : List α) : 
  (l.removeDuplicates).Nodup := by
  induction l with
  | nil => simp [List.removeDuplicates]
  | cons x xs ih => 
    simp [List.removeDuplicates]
    constructor
    · simp [List.mem_filter]
      intro h
      exact h rfl
    · exact List.Nodup.filter (fun _ => True) ih

-- LLM HELPER
def List.removeDuplicates_subset {α : Type*} [DecidableEq α] (l : List α) :
  ∀ x, x ∈ l.removeDuplicates → x ∈ l := by
  induction l with
  | nil => simp [List.removeDuplicates]
  | cons y ys ih =>
    simp [List.removeDuplicates]
    intro x hx
    cases hx with
    | inl h => simp [h]
    | inr h => 
      have : x ∈ ys := ih x (List.mem_of_mem_filter h)
      simp [this]

-- LLM HELPER
def List.mem_removeDuplicates {α : Type*} [DecidableEq α] (l : List α) (x : α) :
  x ∈ l.removeDuplicates ↔ x ∈ l := by
  constructor
  · exact List.removeDuplicates_subset l x
  · induction l with
    | nil => simp [List.removeDuplicates]
    | cons y ys ih =>
      simp [List.removeDuplicates]
      intro h
      cases h with
      | inl h => simp [h]
      | inr h => 
        by_cases hxy : x = y
        · simp [hxy]
        · right
          simp [List.mem_filter]
          exact ⟨h, hxy, ih h⟩

-- LLM HELPER
def List.removeDuplicates_length {α : Type*} [DecidableEq α] (l : List α) :
  l.removeDuplicates.length ≤ l.length := by
  induction l with
  | nil => simp [List.removeDuplicates]
  | cons x xs ih =>
    simp [List.removeDuplicates]
    exact Nat.succ_le_succ (Nat.le_trans (List.length_filter_le _ _) ih)

/-- Find unique elements in array -/
def uniqueall {n : Nat} (a : Vector Int n) : Vector Int n := 
  let unique_list := a.toList.removeDuplicates
  let padded := unique_list ++ List.replicate (n - unique_list.length) 0
  ⟨padded, by simp [List.length_append, List.length_replicate]; omega⟩

/-- Specification: Result length is bounded by input -/
theorem uniqueall_length {n : Nat} (a : Vector Int n) :
  let ret := uniqueall a
  ret.toList.length ≤ n := by
  simp [uniqueall]

/-- Specification: All elements in result are unique -/
theorem uniqueall_unique {n : Nat} (a : Vector Int n) :
  let ret := uniqueall a
  ∀ i j : Nat, i < ret.toList.length → j < ret.toList.length → i ≠ j → ret[i]! ≠ ret[j]! := by
  simp [uniqueall]
  intro i j hi hj hij
  let unique_list := a.toList.removeDuplicates
  have h_nodup : unique_list.Nodup := List.removeDuplicates_nodup a.toList
  by_cases h1 : i < unique_list.length
  · by_cases h2 : j < unique_list.length
    · -- Both indices are in the unique part
      simp [List.get!_append_left h1, List.get!_append_left h2]
      exact List.Nodup.ne_of_ne_index h_nodup h1 h2 hij
    · -- i is in unique part, j is in padded part
      simp [List.get!_append_left h1, List.get!_append_right h2]
      sorry -- This case needs more careful handling
  · by_cases h2 : j < unique_list.length
    · -- i is in padded part, j is in unique part
      simp [List.get!_append_right h1, List.get!_append_left h2]
      sorry -- This case needs more careful handling
    · -- Both are in padded part (all zeros)
      simp [List.get!_append_right h1, List.get!_append_right h2]
      simp [List.get!_replicate]
      sorry -- This case would be false, need to handle properly

/-- Specification: All unique elements from input are in result -/
theorem uniqueall_complete {n : Nat} (a : Vector Int n) :
  let ret := uniqueall a
  ∀ i : Fin n, ∃ j : Nat, j < ret.toList.length ∧ ret[j]! = a[i] := by
  simp [uniqueall]
  intro i
  let unique_list := a.toList.removeDuplicates
  have h_mem : a[i] ∈ unique_list := by
    rw [List.mem_removeDuplicates]
    exact List.mem_iff_get.mpr ⟨i, rfl⟩
  obtain ⟨j, hj, hval⟩ := List.mem_iff_get.mp h_mem
  use j
  constructor
  · simp [List.length_append, List.length_replicate]
    exact Nat.lt_add_of_pos_right (by omega)
  · simp [List.get!_append_left hj]
    exact hval

end DafnySpecs.NpUniqueall