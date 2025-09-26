import Mathlib
-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: Count occurrences of a value in a list
def count_occurrences (lst : List Nat) (val : Nat) : Nat :=
  lst.filter (· = val) |>.length

-- LLM HELPER: Basic properties of vector construction
lemma vector_ofFn_get {α : Type*} {n : Nat} (f : Fin n → α) (i : Fin n) :
  (Vector.ofFn f).get i = f i := by
  simp [Vector.get_ofFn]

-- LLM HELPER: Simple weakest precondition for pure computations
def wp_pure {α : Type*} (x : α) (P : α → Prop) : Prop := P x

-- LLM HELPER: Weakest precondition for bind in Id monad
def wp_id_bind {α β : Type*} (m : Id α) (f : α → Id β) (P : β → Prop) : Prop :=
  wp_pure (Id.run m) (fun a => wp_pure (Id.run (f a)) P)
-- </vc-helpers>

-- <vc-definitions>
def numpy_bincount {n : Nat} (x : Vector Nat n) (max_val : Nat) 
    (h_bounds : ∀ i : Fin n, x.get i ≤ max_val) : Id (Vector Nat (max_val + 1)) :=
  do
  let result := Vector.ofFn (fun i : Fin (max_val + 1) =>
    (x.toList.filter (· = i.val)).length)
  pure result
-- </vc-definitions>

-- <vc-theorems>
theorem numpy_bincount_spec {n : Nat} (x : Vector Nat n) (max_val : Nat) 
    (h_bounds : ∀ i : Fin n, x.get i ≤ max_val) :
    ⦃⌜∀ i : Fin n, x.get i ≤ max_val⌝⦄
    numpy_bincount x max_val h_bounds
    ⦃⇓result => ⌜∀ val : Fin (max_val + 1), 
                   result.get val = (x.toList.filter (· = val.val)).length⌝⦄ := by
  unfold numpy_bincount
  simp only [wp_pure, wp_id_bind]
  intro val
  simp [Vector.get_ofFn, Id.run]
-- </vc-theorems>
