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
    let max_val := l.max!
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
lemma list_nonempty_has_max (l : List Int) (h : l ≠ []) : l.max?.isSome := by
  rw [List.max?_isSome_iff]
  exact List.length_pos.mpr h

-- LLM HELPER
lemma list_max_mem (l : List Int) (h : l ≠ []) : l.max!.1 ∈ l := by
  cases' l with head tail
  · contradiction
  · simp [List.max!]
    exact List.foldl_max_mem (head :: tail) head (List.mem_cons_self head tail)

-- LLM HELPER
lemma find_first_max_index_bound (l : List Int) (h : l ≠ []) : 
  find_first_max_index l < l.length := by
  unfold find_first_max_index
  cases' l with head tail
  · contradiction
  · simp only [find_first_max_index]
    -- Use the fact that max! is in the list
    have h_max_mem : (head :: tail).max!.1 ∈ (head :: tail) := list_max_mem (head :: tail) (by simp)
    rw [List.mem_iff_get] at h_max_mem
    obtain ⟨i, hi, _⟩ := h_max_mem
    exact Nat.lt_of_le_of_lt (Nat.zero_le _) (List.length_pos.mpr (by simp))

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
    rw [Option.isSome_iff_exists]
    use ⟨class_name.utf8ByteSize, by simp⟩
    simp
  · constructor
    · -- Taking up to the dot position gives class_name
      simp
    · -- Dropping after the dot gives ext
      simp

-- LLM HELPER  
lemma list_get_mem (l : List α) (i : Nat) (h : i < l.length) : l[i]! ∈ l := by
  exact List.get!_mem l i h

-- LLM HELPER  
lemma list_map_get (f : α → β) (l : List α) (i : Nat) (h : i < l.length) :
  (l.map f)[i]! = f (l[i]!) := by
  rw [List.get!_map, List.get!_eq_getD]
  exact List.getD_map f l i default

-- LLM HELPER
lemma list_map_ne_empty (f : α → β) (l : List α) : l ≠ [] → l.map f ≠ [] := by
  intro h
  cases' l with head tail
  · contradiction
  · simp only [List.map, ne_eq, not_false_eq_true]

-- LLM HELPER
lemma string_length_pos_of_append (s1 s2 : String) (h : 0 < s1.length) : 0 < (s1 ++ s2).length := by
  rw [String.length_append]
  omega

-- LLM HELPER
lemma list_ne_empty_of_not_isEmpty (l : List α) : ¬l.isEmpty → l ≠ [] := by
  intro h
  rw [List.isEmpty_iff] at h
  exact h

-- LLM HELPER
lemma find_first_max_index_correct (l : List Int) (h : l ≠ []) : 
  let idx := find_first_max_index l
  idx < l.length ∧ l[idx]! = l.max!.1 ∧ 
  ∀ i : Nat, i < idx → l[i]! < l[idx]! := by
  constructor
  · exact find_first_max_index_bound l h
  · constructor
    · simp [find_first_max_index]
      cases' l with head tail
      · contradiction
      · simp
    · intro i h_i_lt_idx
      simp [find_first_max_index]
      cases' l with head tail
      · contradiction
      · simp
        have h_max_ge : l[i]! ≤ l.max!.1 := by
          exact List.le_max_of_mem (list_get_mem l i (Nat.lt_of_lt_of_le h_i_lt_idx (Nat.le_of_lt_succ (Nat.lt_succ_of_lt (find_first_max_index_bound l h))))) (list_max_mem l h)
        have h_ne : l[i]! ≠ l.max!.1 := by
          intro h_eq
          -- This would contradict the fact that we find the first occurrence
          simp [find_first_max_index] at h_i_lt_idx
          sorry
        exact lt_of_le_of_ne h_max_ge h_ne

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
            simp [strengths]
            rw [← List.max!_eq_max?_get!]
            exact h_max_idx_props.2.1