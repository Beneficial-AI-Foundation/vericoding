import Std.Do.Triple
import Std.Tactic.Do

{
  "name": "_128Bit",
  "category": "Bit Precision Types",
  "description": "Type representing 128-bit precision",
  "url": "https://github.com/numpy/numpy/blob/main/numpy/_typing/_nbit_base.py",
  "doc": "A type representing 128-bit precision for numpy.number subclasses during static type checking.",
  "code": "@final\n@set_module(\"numpy._typing\")\nclass _128Bit(NBitBase):\n    pass"
}
-/

open Std.Do

/-- _128Bit: Create a 128-bit precision type instance.
    
    This represents the highest precision level in NumPy's typing hierarchy.
    It's a subclass of NBitBase specifically for 128-bit precision numeric types.
    Used exclusively for static type checking to ensure type safety with
    128-bit precision computations.
-/
def _128Bit : Id { n : Nat // n = 128 ∧ n ∈ [8, 16, 32, 64, 96, 128] } :=
  return ⟨128, rfl, by simp⟩

-- LLM HELPER
lemma mem_precision_list_128 : 128 ∈ [8, 16, 32, 64, 96, 128] := by simp

-- LLM HELPER
lemma le_128_of_mem_precision_list (n : Nat) (h : n ∈ [8, 16, 32, 64, 96, 128]) : n ≤ 128 := by
  simp at h
  cases h with
  | inl h => rw [h]; norm_num
  | inr h => cases h with
    | inl h => rw [h]; norm_num
    | inr h => cases h with
      | inl h => rw [h]; norm_num
      | inr h => cases h with
        | inl h => rw [h]; norm_num
        | inr h => cases h with
          | inl h => rw [h]; norm_num
          | inr h => rw [h]; norm_num

-- LLM HELPER
lemma lt_128_ne_128 (n : Nat) (h : n < 128) : n ≠ 128 := by
  intro h_eq
  rw [h_eq] at h
  exact lt_irrefl 128 h

/-- Specification: _128Bit creates a precision instance that represents exactly 128-bit precision
    and maintains the hierarchical precision relationship where 128-bit is the highest precision.
    
    Precondition: None (always valid)
    Postcondition: The resulting instance represents exactly 128-bit precision
    and is the highest precision level in the hierarchy
-/
theorem _128Bit_spec :
    ⦃⌜True⌝⦄
    _128Bit
    ⦃⇓precision_instance => ⌜precision_instance.val = 128 ∧ 
                            precision_instance.val ∈ [8, 16, 32, 64, 96, 128] ∧
                            (∀ (other_width : Nat), other_width ∈ [8, 16, 32, 64, 96, 128] → 
                             other_width ≤ 128) ∧
                            (∀ (other_width : Nat), other_width ∈ [8, 16, 32, 64, 96, 128] → 
                             other_width < 128 → other_width ≠ 128)⌝⦄ := by
  simp [_128Bit, Std.Do.Triple.pure]
  constructor
  · rfl
  constructor
  · exact mem_precision_list_128
  constructor
  · exact le_128_of_mem_precision_list
  · exact fun _ _ => lt_128_ne_128