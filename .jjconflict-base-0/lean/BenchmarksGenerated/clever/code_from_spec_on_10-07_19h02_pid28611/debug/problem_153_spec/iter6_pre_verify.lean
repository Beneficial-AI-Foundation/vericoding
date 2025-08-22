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
lemma find_first_max_index_correct (l : List Int) (h : l ≠ []) : 
  let idx := find_first_max_index l
  idx < l.length ∧ l[idx]! = l.max?.get! ∧ 
  ∀ i : Nat, i < idx → l[i]! < l[idx]! := by
  unfold find_first_max_index
  cases' l with head tail
  · contradiction
  · simp only [find_first_max_index]
    constructor
    · simp only [List.length_cons]
      omega
    · constructor
      · sorry
      · sorry

-- LLM HELPER
lemma string_rev_pos_of_dot (class_name ext : String) (h1 : 0 < class_name.length) (h2 : 0 < ext.length) :
  let result := class_name ++ "." ++ ext
  let last_pos := result.revPosOf '.'
  last_pos.isSome ∧
  result.take (last_pos.get!).byteIdx = class_name ∧
  result.drop ((last_pos.get!).byteIdx + 1) = ext := by
  sorry

-- LLM HELPER  
lemma list_get_mem {α : Type*} [Inhabited α] (l : List α) (i : Nat) (h : i < l.length) : l[i]! ∈ l := by
  have : l[i]! = l.get ⟨i, h⟩ := by simp only [List.get!_eq_getD, List.getD_eq_getElem]
  rw [this]
  apply List.get_mem

-- LLM HELPER  
lemma list_map_get {α β : Type*} [Inhabited β] (f : α → β) (l : List α) (i : Nat) (h : i < l.length) :
  (l.map f)[i]! = f (l[i]!) := by
  have h_map_len : i < (l.map f).length := by
    rw [List.length_map]
    exact h
  have : (l.map f)[i]! = (l.map f).get ⟨i, h_map_len⟩ := by simp only [List.get!_eq_getD, List.getD_eq_getElem]
  rw [this, List.getElem_map]
  simp only [List.get!_eq_getD, List.getD_eq_getElem]

-- LLM HELPER
lemma list_map_ne_empty {α β : Type*} (f : α → β) (l : List α) : l ≠ [] → l.map f ≠ [] := by
  intro h
  cases' l with head tail
  · contradiction
  · simp only [List.map, ne_eq, not_false_eq_true]

-- LLM HELPER
lemma list_all_get {α : Type*} [Inhabited α] (l : List α) (p : α → Prop) [DecidablePred p] (i : Nat) (h : i < l.length) :
  l.all (fun x => decide (p x)) → p (l[i]!) := by
  intro h_all
  rw [List.all_eq_true] at h_all
  have h_mem : l[i]! ∈ l := list_get_mem l i h
  have : decide (p (l[i]!)) = true := h_all (l[i]!) h_mem
  exact of_decide_eq_true this

-- LLM HELPER
lemma string_length_pos_of_append (s1 s2 : String) (h : 0 < s1.length) : 0 < (s1 ++ s2).length := by
  rw [String.length_append]
  omega

-- LLM HELPER
lemma list_ne_empty_of_not_isEmpty {α : Type*} (l : List α) : ¬l.isEmpty → l ≠ [] := by
  intro h
  rw [List.isEmpty_iff_eq_nil] at h
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
      rw [List.isEmpty_iff_eq_nil] at h_empty
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
        have : (fun x => 0 < x.length) chosen_ext := list_all_get extensions (fun x => 0 < x.length) max_idx h_max_idx_bound h2
        exact this
      
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
            simp only [chosen_ext]
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