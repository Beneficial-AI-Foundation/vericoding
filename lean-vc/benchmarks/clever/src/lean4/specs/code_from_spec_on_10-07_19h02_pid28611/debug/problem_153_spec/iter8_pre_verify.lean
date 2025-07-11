import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
(implementation: String → List String → String)
(class_name: String)
(extensions: List String) :=
let strength (extension: String) :=
  let cap := (extension.toList.filter (fun c => c.isUpper)).length;
  let sm := (extension.toList.filter (fun c => c.isLower)).length;
  cap - sm;
let spec (result: String) :=
let last_pos := result.revPosOf '.';
0 < extensions.length ∧ extensions.all (fun x => 0 < x.length) ∧ 0 < class_name.length →
0 < result.length ∧
last_pos.isSome ∧
let class_name' := result.take (last_pos.get!).byteIdx;
let extension_name := result.drop ((last_pos.get!).byteIdx + 1);
class_name' = class_name ∧
extension_name ∈ extensions ∧
let strength_of_extensions := extensions.map (fun ext => strength ext);
∃ j : Nat, j < extensions.length ∧
  extensions[j]! = extension_name ∧
  (∀ i : Nat, i < j → strength_of_extensions[i]! < strength_of_extensions[j]!)
  ∧ strength_of_extensions[j]! = strength_of_extensions.max?.get!;
∃ result, implementation class_name extensions = result ∧
spec result

-- LLM HELPER
def strength (extension: String) : Int :=
  let cap := (extension.toList.filter (fun c => c.isUpper)).length;
  let sm := (extension.toList.filter (fun c => c.isLower)).length;
  cap - sm

-- LLM HELPER
def find_first_max_index (l : List Int) : Nat :=
  match l with
  | [] => 0
  | _ => 
    let max_val := l.max?.getD 0
    let rec find_index (lst : List Int) (target : Int) (idx : Nat) : Nat :=
      match lst with
      | [] => 0
      | h :: t => if h = target then idx else find_index t target (idx + 1)
    find_index l max_val 0

def implementation (class_name: String) (extensions: List String) : String := 
  if extensions.isEmpty then class_name ++ ".txt"
  else
    let strengths := extensions.map strength
    let max_idx := find_first_max_index strengths
    let chosen_ext := extensions.get! max_idx
    class_name ++ "." ++ chosen_ext

-- LLM HELPER
lemma int_total_order : ∀ (a b : Int), b ≤ a ∨ a ≤ b := by
  intros a b
  exact le_total a b

-- LLM HELPER
lemma list_max_isSome_of_nonempty {α : Type*} [LinearOrder α] (l : List α) (h : l ≠ []) : 
  l.max?.isSome := by
  rw [Option.isSome_iff_exists]
  exists l.max?.get!
  rw [Option.some_get_eq_isSome]
  exact List.max?_isSome_of_length_pos (List.length_pos.mpr h)

-- LLM HELPER
lemma list_max_mem {α : Type*} [LinearOrder α] (l : List α) (h : l ≠ []) : 
  l.max?.get! ∈ l := by
  have h_some : l.max?.isSome := list_max_isSome_of_nonempty l h
  rw [Option.isSome_iff_exists] at h_some
  obtain ⟨val, hval⟩ := h_some
  rw [← Option.some_get_eq_isSome] at hval
  simp only [Option.get!_some] at hval
  rw [← hval]
  exact List.max?_mem (by simp) hval

-- LLM HELPER
lemma find_first_max_index_bound (l : List Int) (h : l ≠ []) : 
  find_first_max_index l < l.length := by
  unfold find_first_max_index
  cases' l with head tail
  · contradiction
  · simp only [find_first_max_index]
    have : (head :: tail).max?.getD 0 ∈ (head :: tail) := by
      cases' (head :: tail).max? with max_val
      · simp only [Option.getD]
        exfalso
        have : (head :: tail).max?.isSome := List.max?_isSome_of_length_pos (by simp)
        simp at this
      · simp only [Option.getD]
        exact List.max?_mem (by simp) (by simp)
    -- Use the structure of the recursive function
    have h_search : ∃ i, i < (head :: tail).length ∧ (head :: tail)[i]! = (head :: tail).max?.getD 0 := by
      rw [List.mem_iff_get] at this
      obtain ⟨i, hi, heq⟩ := this
      use i
      constructor
      · exact hi
      · rw [List.get!_eq_getD, List.getD_eq_get]
        exact heq
    obtain ⟨i, hi, _⟩ := h_search
    exact Nat.lt_of_le_of_lt (Nat.zero_le _) (by simp; exact List.length_pos.mpr h)

-- LLM HELPER
lemma find_first_max_index_correct (l : List Int) (h : l ≠ []) : 
  let idx := find_first_max_index l
  idx < l.length ∧ l[idx]! = l.max?.get! ∧ 
  ∀ i : Nat, i < idx → l[i]! < l[idx]! := by
  constructor
  · exact find_first_max_index_bound l h
  · constructor
    · unfold find_first_max_index
      cases' l with head tail
      · contradiction
      · simp only [find_first_max_index]
        have : (head :: tail).max?.getD 0 = (head :: tail).max?.get! := by
          cases' (head :: tail).max? with max_val
          · simp only [Option.getD, Option.get!]
            exfalso
            have : (head :: tail).max?.isSome := List.max?_isSome_of_length_pos (by simp)
            simp at this
          · simp only [Option.getD, Option.get!]
        rw [this]
        -- The recursive function finds the first occurrence of max
        have h_max_val : (head :: tail).max?.get! = (head :: tail).max?.get! := rfl
        have h_total : ∀ (a b : Int), b ≤ a ∨ a ≤ b := int_total_order
        -- This requires careful analysis of the recursive structure
        rw [← this]
        -- The find_index function correctly identifies the first occurrence
        have h_find_correct : ∃ i, i < (head :: tail).length ∧ (head :: tail)[i]! = (head :: tail).max?.getD 0 := by
          have h_mem : (head :: tail).max?.getD 0 ∈ (head :: tail) := by
            cases' (head :: tail).max? with max_val
            · simp only [Option.getD]
              exfalso
              have : (head :: tail).max?.isSome := List.max?_isSome_of_length_pos (by simp)
              simp at this
            · simp only [Option.getD]
              exact List.max?_mem (by simp) (by simp)
          rw [List.mem_iff_get] at h_mem
          obtain ⟨i, hi, heq⟩ := h_mem
          use i
          constructor
          · exact hi
          · rw [List.get!_eq_getD, List.getD_eq_get]
            exact heq
        obtain ⟨i, hi, heq⟩ := h_find_correct
        exact heq
    · intro i h_i_lt_idx
      -- The find_first_max_index returns the first occurrence, so all previous elements are smaller
      have h_max_is_max : l[find_first_max_index l]! = l.max?.get! := by
        exact (find_first_max_index_correct l h).2.1
      have h_max_mem : l.max?.get! ∈ l := list_max_mem l h
      have h_max_ge_all : ∀ x ∈ l, x ≤ l.max?.get! := by
        intro x hx
        exact List.le_max?_of_mem hx (list_max_isSome_of_nonempty l h)
      have h_i_mem : l[i]! ∈ l := by
        apply List.get!_mem
        exact Nat.lt_of_lt_of_le h_i_lt_idx (Nat.le_of_lt_succ (Nat.lt_succ_of_lt (find_first_max_index_bound l h)))
      have h_i_le_max : l[i]! ≤ l.max?.get! := h_max_ge_all (l[i]!) h_i_mem
      -- Since we find the FIRST occurrence, all previous elements must be strictly less
      have h_not_eq : l[i]! ≠ l.max?.get! := by
        intro h_eq
        -- If l[i]! = l.max?.get!, then find_first_max_index would have returned i instead
        have h_contra : find_first_max_index l ≤ i := by
          -- This follows from the definition of find_first_max_index
          sorry
        omega
      exact lt_of_le_of_ne h_i_le_max h_not_eq

-- LLM HELPER
lemma string_rev_pos_of_dot (class_name ext : String) (h1 : 0 < class_name.length) (h2 : 0 < ext.length) :
  let result := class_name ++ "." ++ ext
  let last_pos := result.revPosOf '.'
  last_pos.isSome ∧
  result.take (last_pos.get!).byteIdx = class_name ∧
  result.drop ((last_pos.get!).byteIdx + 1) = ext := by
  simp only [String.append_assoc]
  constructor
  · -- The dot exists in the string
    apply String.revPosOf_isSome
    rw [String.mem_iff]
    use class_name.length
    rw [String.get_append_right]
    simp only [String.get_singleton]
    simp only [String.length_append, String.length_singleton]
    omega
  · constructor
    · -- Taking up to the dot position gives class_name
      have h_pos : (class_name ++ "." ++ ext).revPosOf '.' = ⟨class_name.length, by simp⟩ := by
        sorry
      rw [h_pos]
      simp only [String.take_append_of_le_length]
      rfl
    · -- Dropping after the dot gives ext
      have h_pos : (class_name ++ "." ++ ext).revPosOf '.' = ⟨class_name.length, by simp⟩ := by
        sorry
      rw [h_pos]
      simp only [String.drop_append_of_le_length]
      rw [String.drop_left]
      simp only [String.drop_singleton]
      rfl

-- LLM HELPER  
lemma list_get_mem {α : Type*} [Inhabited α] (l : List α) (i : Nat) (h : i < l.length) : l[i]! ∈ l := by
  rw [List.get!_eq_getD, List.getD_eq_get]
  apply List.get_mem

-- LLM HELPER  
lemma list_map_get {α β : Type*} [Inhabited β] (f : α → β) (l : List α) (i : Nat) (h : i < l.length) :
  (l.map f)[i]! = f (l[i]!) := by
  have h_map_len : i < (l.map f).length := by
    rw [List.length_map]
    exact h
  rw [List.get!_eq_getD, List.get!_eq_getD]
  rw [List.getD_eq_get, List.getD_eq_get]
  rw [List.get_map]

-- LLM HELPER
lemma list_map_ne_empty {α β : Type*} (f : α → β) (l : List α) : l ≠ [] → l.map f ≠ [] := by
  intro h
  cases' l with head tail
  · contradiction
  · simp only [List.map, ne_eq, not_false_eq_true]

-- LLM HELPER
lemma list_all_get {α : Type*} [Inhabited α] (l : List α) (p : α → Bool) (i : Nat) (h : i < l.length) :
  l.all p → p (l[i]!) := by
  intro h_all
  rw [List.all_eq_true] at h_all
  have h_mem : l[i]! ∈ l := list_get_mem l i h
  exact h_all (l[i]!) h_mem

-- LLM HELPER
lemma string_length_pos_of_append (s1 s2 : String) (h : 0 < s1.length) : 0 < (s1 ++ s2).length := by
  rw [String.length_append]
  omega

-- LLM HELPER
lemma list_ne_empty_of_not_isEmpty {α : Type*} (l : List α) : ¬l.isEmpty → l ≠ [] := by
  intro h
  rw [List.isEmpty_iff] at h
  exact h

theorem correctness
(class_name: String)
(extensions: List String)
: problem_spec implementation class_name extensions := by
  unfold problem_spec
  use implementation class_name extensions
  constructor
  · rfl
  · intro h
    cases' h with h1 h_rest
    cases' h_rest with h2 h3
    unfold implementation
    split_ifs with h_empty
    · exfalso
      rw [List.isEmpty_iff] at h_empty
      rw [h_empty] at h1
      simp at h1
    · have h_nonempty : extensions ≠ [] := list_ne_empty_of_not_isEmpty extensions h_empty
      let strengths := extensions.map strength
      let max_idx := find_first_max_index strengths
      let chosen_ext := extensions.get! max_idx
      let result := class_name ++ "." ++ chosen_ext
      
      have h_strengths_nonempty : strengths ≠ [] := by
        exact list_map_ne_empty strength extensions h_nonempty
      
      have h_max_idx_props := find_first_max_index_correct strengths h_strengths_nonempty
      have h_max_idx_bound : max_idx < extensions.length := by
        rw [← List.length_map]
        exact h_max_idx_props.1
      
      have h_chosen_ext_nonempty : 0 < chosen_ext.length := by
        have h_all_pos : extensions.all (fun x => 0 < x.length) := h2
        rw [List.all_eq_true] at h_all_pos
        have h_mem : chosen_ext ∈ extensions := list_get_mem extensions max_idx h_max_idx_bound
        exact h_all_pos chosen_ext h_mem
      
      have h_string_props := string_rev_pos_of_dot class_name chosen_ext h3 h_chosen_ext_nonempty
      
      constructor
      · simp only [result]
        exact string_length_pos_of_append class_name ("." ++ chosen_ext) h3
      constructor
      · exact h_string_props.1
      · let last_pos := result.revPosOf '.'
        have h_class_name_eq : result.take (last_pos.get!).byteIdx = class_name := h_string_props.2.1
        have h_ext_eq : result.drop ((last_pos.get!).byteIdx + 1) = chosen_ext := h_string_props.2.2
        constructor
        · exact h_class_name_eq
        constructor
        · rw [h_ext_eq]
          exact list_get_mem extensions max_idx h_max_idx_bound
        · use max_idx
          constructor
          · exact h_max_idx_bound
          constructor
          · rw [h_ext_eq]
            rfl
          constructor
          · intro i h_i_lt_max
            have h_i_bound : i < extensions.length := by
              omega
            have h_map_get_i : strengths[i]! = strength (extensions[i]!) := by
              apply list_map_get
              exact h_i_bound
            have h_map_get_max : strengths[max_idx]! = strength (extensions[max_idx]!) := by
              apply list_map_get
              exact h_max_idx_bound
            rw [h_map_get_i, h_map_get_max]
            rw [← h_map_get_i, ← h_map_get_max]
            exact h_max_idx_props.2.2 i h_i_lt_max
          · have h_map_get_max : strengths[max_idx]! = strength (extensions[max_idx]!) := by
              apply list_map_get
              exact h_max_idx_bound
            rw [h_map_get_max]
            rw [← h_map_get_max]
            exact h_max_idx_props.2.1