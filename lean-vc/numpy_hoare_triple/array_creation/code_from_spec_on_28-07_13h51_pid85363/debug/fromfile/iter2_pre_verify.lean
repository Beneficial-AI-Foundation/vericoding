import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

-- Abstract file representation for specification purposes
structure FileData where
  content : List Float
  valid : Bool

-- LLM HELPER
def read_from_file_content (content : List Float) (offset : Nat) (n : Nat) : List Float :=
  (content.drop offset).take n

-- LLM HELPER
def list_to_vector {n : Nat} (l : List Float) (h : l.length = n) : Vector Float n :=
  ⟨l, h⟩

-- LLM HELPER
def problem_spec (impl : Nat → FileData → Int → Nat → Id (Vector Float n)) (n : Nat) (file : FileData) (count : Int) (offset : Nat) : Prop :=
  file.valid = true ∧
  (count = n ∨ count = -1) ∧
  offset ≤ file.content.length ∧
  file.content.length - offset ≥ n →
  ∀ result, impl n file count offset = ⟨result⟩ →
  (∀ i : Fin n, result.get i = file.content[offset + i.val]! ∧ n ≤ file.content.length - offset)

/-- Construct a vector from data in a file -/
def fromfile (n : Nat) (file : FileData) (count : Int) (offset : Nat) : Id (Vector Float n) :=
  let data := read_from_file_content file.content offset n
  let padded_data := data ++ List.replicate (n - data.length) 0.0
  let final_data := padded_data.take n
  have h : final_data.length = n := by
    simp [final_data, padded_data]
    rw [List.length_take]
    simp [List.length_append, List.length_replicate]
    omega
  ⟨list_to_vector final_data h⟩

-- LLM HELPER
lemma list_get_drop_take (l : List Float) (offset : Nat) (n : Nat) (i : Nat) 
    (hi : i < n) (hbound : offset + i < l.length) :
    ((l.drop offset).take n)[i]! = l[offset + i]! := by
  rw [List.getElem!_eq_getElem_get?]
  rw [List.getElem!_eq_getElem_get?]
  simp [List.get?_take, List.get?_drop]
  simp [hbound, hi]
  rfl

-- LLM HELPER
lemma sufficient_data_length (content : List Float) (offset n : Nat) 
    (h : content.length - offset ≥ n) (hoff : offset ≤ content.length) :
    (content.drop offset).length ≥ n := by
  rw [List.length_drop]
  omega

theorem correctness (n : Nat) (file : FileData) (count : Int) (offset : Nat) : problem_spec fromfile n file count offset := by
  intro h_premises result h_result
  have ⟨h_valid, h_count, h_offset, h_sufficient⟩ := h_premises
  simp [fromfile] at h_result
  cases h_result
  intro i
  constructor
  · simp [list_to_vector, Vector.get]
    have data_def : read_from_file_content file.content offset n = (file.content.drop offset).take n := rfl
    have sufficient_len : (file.content.drop offset).length ≥ n := 
      sufficient_data_length file.content offset n h_sufficient h_offset
    have take_len : ((file.content.drop offset).take n).length = n := by
      rw [List.length_take]
      simp [sufficient_len]
    have padded_eq : read_from_file_content file.content offset n ++ List.replicate (n - (read_from_file_content file.content offset n).length) 0.0 = read_from_file_content file.content offset n := by
      rw [data_def, take_len]
      simp
    have final_eq : (read_from_file_content file.content offset n ++ List.replicate (n - (read_from_file_content file.content offset n).length) 0.0).take n = read_from_file_content file.content offset n := by
      rw [padded_eq, data_def, take_len]
      exact List.take_left_of_le (le_refl n)
    rw [final_eq, data_def]
    exact list_get_drop_take file.content offset n i.val i.isLt (by omega)
  · exact h_sufficient