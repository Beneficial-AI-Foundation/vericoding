import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

-- LLM HELPER
def String.findLastOccurrence (s : String) (sep : String) : Option Nat :=
  let sepLen := sep.length
  if sepLen = 0 then none
  else
    let rec findLast (pos : Nat) (lastFound : Option Nat) : Option Nat :=
      if pos + sepLen > s.length then lastFound
      else
        let substr := s.extract ⟨pos⟩ ⟨pos + sepLen⟩
        if substr = sep then
          findLast (pos + 1) (some pos)
        else
          findLast (pos + 1) lastFound
    findLast 0 none
  termination_by s.length - pos

-- LLM HELPER
def String.rpartitionSingle (s : String) (sep : String) : (String × String × String) :=
  match s.findLastOccurrence sep with
  | none => ("", "", s)
  | some pos => 
    let before := s.extract ⟨0⟩ ⟨pos⟩
    let after := s.extract ⟨pos + sep.length⟩ ⟨s.length⟩
    (before, sep, after)

/-- numpy.strings.rpartition: Partition each element in a around the right-most separator.

    Partitions each string in the input vector at the last occurrence of the separator.
    Returns a 3-tuple of vectors: (before_separator, separator, after_separator).
    
    For each element in the input array, splits the element at the last occurrence
    of the separator, and returns three vectors containing the part before the separator,
    the separator itself, and the part after the separator. If the separator is not found,
    the third vector contains the whole string, and the first and second vectors contain
    empty strings.

    From NumPy documentation:
    - Parameters: a (array_like with StringDType), sep (array_like with StringDType)
    - Returns: 3-tuple of ndarrays with StringDType

    Mathematical Properties:
    1. Right partition semantics: For each string s, if sep occurs at position i (rightmost), then:
       - before = s[0:i]
       - separator = sep (if found) or "" (if not found)
       - after = s[i+len(sep):] (if found) or "" (if not found)
    2. Completeness: before ++ separator ++ after = original string (when sep is found)
    3. Last occurrence: Only splits at the last occurrence of sep
    4. Not found case: If sep not in string, returns ("", "", original_string)
    5. Preserves vector length: All three result vectors have the same length as input
-/
def rpartition {n : Nat} (a : Vector String n) (sep : String) : Id (Vector String n × Vector String n × Vector String n) :=
  let results := a.map (fun s => s.rpartitionSingle sep)
  let before := results.map (fun ⟨b, _, _⟩ => b)
  let separator := results.map (fun ⟨_, s, _⟩ => s)
  let after := results.map (fun ⟨_, _, a⟩ => a)
  (before, separator, after)

-- LLM HELPER
lemma String.rpartitionSingle_correct (s : String) (sep : String) :
  let (before, separator, after) := s.rpartitionSingle sep
  before ++ separator ++ after = s ∧
  (separator = sep ∨ separator = "") ∧
  (separator = "" → before = "" ∧ after = s) := by
  simp [String.rpartitionSingle]
  split
  · simp
  · simp
    constructor
    · rfl
    · constructor
      · left
        rfl
      · intro h
        exact h

-- LLM HELPER
lemma Vector.map_length_preserved {α β : Type*} {n : Nat} (v : Vector α n) (f : α → β) :
  (v.map f).length = n := by
  rw [Vector.map, Vector.length_mk]
  simp [List.length_map]

-- LLM HELPER
lemma Vector.get_map_triple_fst {α β γ δ : Type*} {n : Nat} (v : Vector α n) (f : α → β × γ × δ) (i : Fin n) :
  (v.map (fun x => (f x).1)).get i = (f (v.get i)).1 := by
  simp [Vector.get_map]

-- LLM HELPER
lemma Vector.get_map_triple_snd {α β γ δ : Type*} {n : Nat} (v : Vector α n) (f : α → β × γ × δ) (i : Fin n) :
  (v.map (fun x => (f x).2.1)).get i = (f (v.get i)).2.1 := by
  simp [Vector.get_map]

-- LLM HELPER
lemma Vector.get_map_triple_thd {α β γ δ : Type*} {n : Nat} (v : Vector α n) (f : α → β × γ × δ) (i : Fin n) :
  (v.map (fun x => (f x).2.2)).get i = (f (v.get i)).2.2 := by
  simp [Vector.get_map]

/-- Specification: numpy.strings.rpartition returns a 3-tuple of vectors where each
    element is partitioned around the last occurrence of the separator.

    Mathematical Properties:
    1. Right partition correctness: For each index i, the result satisfies rpartition semantics
    2. Completeness: When separator is found, concatenation reconstructs original string
    3. Last occurrence: Only the last occurrence of separator is used for partitioning
    4. Not found case: When separator is not found, returns ("", "", original)
    5. Preserves vector length: All result vectors have the same length as input
    6. Separator consistency: The separator part contains the actual separator or empty string

    Precondition: True (no special preconditions for string partitioning)
    Postcondition: For all indices i, the partition satisfies the rpartition semantics
-/
theorem rpartition_spec {n : Nat} (a : Vector String n) (sep : String) :
    ⦃⌜True⌝⦄
    rpartition a sep
    ⦃⇓result => ⌜∀ i : Fin n, 
                   let original := a.get i
                   let before_i := result.fst.get i
                   let sep_i := result.2.fst.get i
                   let after_i := result.2.snd.get i
                   -- Partition property: reconstructs original string
                   before_i ++ sep_i ++ after_i = original ∧
                   -- Separator correctness: either the separator or empty string
                   (sep_i = sep ∨ sep_i = "") ∧
                   -- If separator is not found, first two parts are empty and after contains whole string
                   (sep_i = "" → before_i = "" ∧ after_i = original)⌝⦄ := by
  simp [rpartition, wp_eta]
  intro i
  have h := String.rpartitionSingle_correct (a.get i) sep
  simp [Vector.get_map_triple_fst, Vector.get_map_triple_snd, Vector.get_map_triple_thd]
  exact h