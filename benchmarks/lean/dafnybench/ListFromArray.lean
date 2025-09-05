/-
  Functional Lists and Imperative Arrays
  
  Ported from Dafny specification: CVS-handout1_tmp_tmptm52no3k_2_spec.dfy
  
  This module implements conversion between functional lists and imperative arrays.
-/

import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- Functional list datatype -/
inductive FList (α : Type) where
  | nil : FList α
  | cons : α → FList α → FList α

namespace FList

/-- Length of a functional list -/
def length {α : Type} : FList α → Nat
  | nil => 0
  | cons _ t => 1 + length t

/-- Membership predicate for functional lists -/
def mem {α : Type} [BEq α] : FList α → α → Bool
  | nil, _ => false
  | cons h t, x => if h == x then true else mem t x

/-- Get element at index i in the list -/
def get {α : Type} [Inhabited α] : (l : FList α) → (i : Nat) → i < length l → α
  | cons h _, 0, _ => h
  | cons _ t, i + 1, h => get t i (by
    simp [length] at h
    omega)
  | nil, _, h => absurd h (by simp [length])

end FList

/-- Convert an array to a functional list -/
def fromArray {α : Type} (a : Array α) : FList α := sorry

/-- Specification: fromArray preserves length, elements, and membership -/
theorem fromArray_spec {α : Type} [BEq α] [Inhabited α] (a : Array α) :
  ⦃⌜a.size ≥ 0⌝⦄ 
  (pure (fromArray a) : Id _)
  ⦃⇓result => ⌜FList.length result = a.size ∧
    (∀ i h, FList.get result i h = a[i]!) ∧
    (∀ x, FList.mem result x = true → ∃ i, i < a.size ∧ a[i]! = x)⌝⦄ := by
  mvcgen [fromArray]
  sorry
