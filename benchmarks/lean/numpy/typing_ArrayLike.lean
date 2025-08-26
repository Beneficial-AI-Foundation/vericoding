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

/-- Convert an ArrayLike object to a Vector by flattening its structure -/
def toVector {T : Type} (arraylike : ArrayLike T) : Id (Σ n : Nat, Vector T n) :=
  sorry

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
  sorry