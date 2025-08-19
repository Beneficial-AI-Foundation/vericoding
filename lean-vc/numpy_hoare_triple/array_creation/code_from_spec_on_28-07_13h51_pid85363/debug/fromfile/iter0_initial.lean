import Std.Do.Triple
import Std.Tactic.Do

{
  "name": "numpy.fromfile",
  "category": "From existing data",
  "description": "Construct an array from data in a text or binary file",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.fromfile.html",
  "doc": "\nConstruct an array from data in a text or binary file.\n\nParameters\n----------\nfile : file or str or Path\n    Open file object or filename.\ndtype : data-type\n    Data type of the returned array. For binary files, it is used to determine the size and byte-order \n    of the items in the file. Most builtin numeric types are supported and extension types may be supported.\ncount : int\n    Number of items to read. -1 means all items (i.e., the complete file).\nsep : str\n    Separator between items if file is a text file. Empty (\"\") separator means the file should be \n    treated as binary. Spaces (\" \") in the separator match zero or more whitespace characters.\noffset : int\n    The offset (in bytes) from the file's current position. Defaults to 0. Only permitted for binary files.\nlike : array_like, optional\n    Reference object to allow the creation of arrays which are not NumPy arrays.\n\nReturns\n-------\narr : ndarray\n    Array of data from the file.\n\nNotes\n-----\nDo not rely on the combination of tofile and fromfile for data storage, as the binary files generated \nare not platform independent. In particular, no byte-order or data-type information is saved.\n",
  "code": "@array_function_dispatch(_fromfile_dispatcher)\ndef fromfile(file, dtype=float, count=-1, sep='', offset=0, *, like=None):\n    \"\"\"\n    Construct an array from data in a text or binary file.\n    \"\"\"\n    if like is not None:\n        return _fromfile_with_like(\n            file, dtype=dtype, count=count, sep=sep, offset=offset, like=like\n        )\n\n    if isinstance(file, os.PathLike):\n        file = os.fspath(file)\n    return _core_fromfile(file, dtype, count, sep, offset)",
  "signature": "numpy.fromfile(file, dtype=float, count=-1, sep='', offset=0, *, like=None)"
}
-/


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

/-- Specification: fromfile reads data from a file into a vector -/
theorem fromfile_spec (n : Nat) (file : FileData) (count : Int) (offset : Nat)
    (h_valid : file.valid = true)
    (h_count : count = n ∨ count = -1)
    (h_offset : offset ≤ file.content.length)
    (h_sufficient : file.content.length - offset ≥ n) :
    ⦃⌜file.valid = true ∧
      (count = n ∨ count = -1) ∧
      offset ≤ file.content.length ∧
      file.content.length - offset ≥ n⌝⦄
    fromfile n file count offset
    ⦃⇓result => ⌜∀ i : Fin n,
      result.get i = file.content[offset + i.val]! ∧
      n ≤ file.content.length - offset⌝⦄ := by
  simp [fromfile]
  constructor
  · constructor
    · exact h_valid
    · constructor
      · exact h_count
      · constructor
        · exact h_offset
        · exact h_sufficient
  · intro i
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