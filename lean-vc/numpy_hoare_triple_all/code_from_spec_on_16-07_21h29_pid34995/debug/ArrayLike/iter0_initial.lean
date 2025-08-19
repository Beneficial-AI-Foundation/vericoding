import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
{
  "name": "ArrayLike",
  "category": "Core Type Aliases",
  "description": "Union type representing objects that can be converted to arrays",
  "url": "https://numpy.org/doc/stable/reference/typing.html#numpy.typing.ArrayLike",
  "doc": "A union type representing objects that can be coerced into an ndarray.\n\nAmong others this includes the likes of:\n- Scalars\n- (Nested) sequences\n- Objects implementing the __array__ protocol\n\nThe ArrayLike type tries to avoid creating object arrays by excluding certain types that would otherwise be valid. For example, ArrayLike does not include arbitrary sequences of strings to prevent string sequences from being interpreted as object arrays.",
  "code": "# From numpy._typing._array_like.py\n_ArrayLike = Union[\n    _SupportsArray[dtype[_ScalarT]],\n    _NestedSequence[_SupportsArray[dtype[_ScalarT]]],\n    # Accept also bare dtypes\n    # Sequence[Sequence] ... e.g. [[1, 2], [3, 4]]\n    _FiniteNestedSequence[_NumberLike | _BoolLike],\n    # Mypy can't handle extended precision datatypes\n    # _FiniteNestedSequence[str | bytes | _ExtendedPrecision],\n    _FiniteNestedSequence[str | bytes],\n]\n\n# The actual ArrayLike type\nArrayLike = _ArrayLike[Any]"
}
-/

/-- A union type representing objects that can be coerced into a Vector.
    Includes scalars, sequences, and nested sequences. -/
inductive ArrayLike (T : Type) : Type where
  /-- A single scalar value that becomes a 1-element vector -/
  | scalar : T → ArrayLike T
  /-- A flat sequence of values -/
  | sequence : {n : Nat} → Vector T n → ArrayLike T
  /-- A nested sequence (matrix) that gets flattened -/
  | nestedSequence : {rows cols : Nat} → Vector (Vector T cols) rows → ArrayLike T

-- LLM HELPER
def vectorAppend {T : Type} {n m : Nat} (v1 : Vector T n) (v2 : Vector T m) : Vector T (n + m) :=
  ⟨v1.toList ++ v2.toList, by simp [Vector.toList_length]⟩

-- LLM HELPER
def flattenMatrix {T : Type} {rows cols : Nat} (mat : Vector (Vector T cols) rows) : Vector T (rows * cols) :=
  match rows with
  | 0 => ⟨[], by simp⟩
  | n + 1 => 
    let firstRow := mat.get ⟨0, Nat.zero_lt_succ n⟩
    let restRows := ⟨(List.range n).map (fun i => mat.get ⟨i + 1, Nat.succ_lt_succ (Nat.lt_of_succ_le (List.mem_range.mp (List.mem_of_mem_map _ (List.mem_range.mpr (Nat.lt_succ_iff.mpr (Nat.le_refl _))))))⟩), by simp⟩
    have : cols + n * cols = (n + 1) * cols := by ring
    this ▸ vectorAppend firstRow (flattenMatrix restRows)

/-- Convert an ArrayLike object to a Vector by flattening its structure -/
def toVector {T : Type} (arraylike : ArrayLike T) : Id (Σ n : Nat, Vector T n) :=
  match arraylike with
  | ArrayLike.scalar x => ⟨1, ⟨[x], rfl⟩⟩
  | ArrayLike.sequence v => ⟨v.size, v⟩
  | ArrayLike.nestedSequence mat => ⟨mat.size * (if mat.size > 0 then (mat.get ⟨0, Nat.pos_iff_ne_zero.mpr (Nat.not_eq_zero_of_zero_lt (Nat.pos_iff_ne_zero.mp (Nat.zero_lt_of_ne_zero (fun h => Nat.lt_irrefl 0 (h ▸ Nat.zero_lt_of_ne_zero h)))))⟩).size else 0), 
    if h : mat.size > 0 then
      let cols := (mat.get ⟨0, h⟩).size
      have : ∀ i : Fin mat.size, (mat.get i).size = cols := by
        intro i
        cases' i with val hval
        simp [cols]
      flattenMatrix mat
    else ⟨[], by simp [h]⟩⟩

/-- Specification: toVector correctly converts ArrayLike objects to vectors -/
theorem toVector_spec {T : Type} (arraylike : ArrayLike T) :
    ⦃⌜True⌝⦄
    toVector arraylike
    ⦃⇓result => ⌜
      (match arraylike with
        | ArrayLike.scalar x => result.1 = 1 ∧ (∃ h : 0 < result.1, result.2.get ⟨0, h⟩ = x)
        | ArrayLike.sequence v => result.1 = v.size ∧ (∀ i : Fin v.size, ∃ h : i.val < result.1, result.2.get ⟨i.val, h⟩ = v.get i)
        | ArrayLike.nestedSequence mat => 
            (∃ total_size : Nat, result.1 = total_size) ∧
            (∀ i : Fin mat.size, ∀ j : Fin (mat.get i).size,
              ∃ k : Fin result.1, result.2.get k = (mat.get i).get j))⌝⦄ := by
  cases arraylike with
  | scalar x =>
    simp [toVector, spec_ret]
    constructor
    · rfl
    · use Nat.zero_lt_one
      simp [Vector.get]
  | sequence v =>
    simp [toVector, spec_ret]
    constructor
    · rfl
    · intro i
      use i.2
      simp
  | nestedSequence mat =>
    simp [toVector, spec_ret]
    constructor
    · use mat.size * (if mat.size > 0 then (mat.get ⟨0, by simp⟩).size else 0)
      rfl
    · intro i j
      by_cases h : mat.size > 0
      · simp [h]
        use ⟨i.val * (mat.get ⟨0, h⟩).size + j.val, by simp⟩
        simp [flattenMatrix]
      · simp [h]
        exfalso
        have : i.val < mat.size := i.2
        have : mat.size = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_not_gt h)
        rw [this] at i.2
        exact Nat.lt_irrefl 0 i.2