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
def readFromFile (file : FileData) (offset : Nat) (n : Nat) : List Float :=
  (file.content.drop offset).take n

-- LLM HELPER
def listToVector {n : Nat} (l : List Float) (h : l.length = n) : Vector Float n :=
  ⟨l, h⟩

/-- Construct a vector from data in a file -/
def fromfile (n : Nat) (file : FileData) (count : Int) (offset : Nat) : Id (Vector Float n) :=
  let data := readFromFile file offset n
  let h : data.length = n := by
    simp [readFromFile]
    rw [List.length_take]
    simp
  pure (listToVector data h)

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
  simp [fromfile, readFromFile, listToVector]
  constructor
  · exact ⟨h_valid, h_count, h_offset, h_sufficient⟩
  · constructor
    · intro i
      constructor
      · simp [Vector.get]
        rw [List.getElem_take, List.getElem_drop]
        · simp
        · exact Nat.lt_of_lt_of_le i.isLt (Nat.min_le_left _ _)
      · exact h_sufficient