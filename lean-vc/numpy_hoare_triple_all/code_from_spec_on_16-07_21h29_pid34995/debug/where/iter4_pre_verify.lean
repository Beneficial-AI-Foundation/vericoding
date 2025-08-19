import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

-- LLM HELPER
def select_element (cond : Bool) (x y : Float) : Float :=
  if cond then x else y

-- LLM HELPER
def Vector.zipWith3 {α β γ δ : Type*} {n : Nat} (f : α → β → γ → δ) (a : Vector α n) (b : Vector β n) (c : Vector γ n) : Vector δ n :=
  Vector.ofFn (fun i => f (a.get i) (b.get i) (c.get i))

-- LLM HELPER
theorem Vector.get_zipWith3 {α β γ δ : Type*} {n : Nat} (f : α → β → γ → δ) (a : Vector α n) (b : Vector β n) (c : Vector γ n) (i : Fin n) :
    (Vector.zipWith3 f a b c).get i = f (a.get i) (b.get i) (c.get i) := by
  simp [Vector.zipWith3]

/-- Return elements chosen from x or y depending on condition.
    For each position i, if condition[i] is True, take x[i], otherwise take y[i]. -/
def numpy_where {n : Nat} (condition : Vector Bool n) (x y : Vector Float n) : Id (Vector Float n) :=
  do
    let result := Vector.zipWith3 select_element condition x y
    return result

/-- Specification: numpy_where returns an array where elements are chosen from x when condition is True,
    and from y when condition is False. -/
theorem numpy_where_spec {n : Nat} (condition : Vector Bool n) (x y : Vector Float n) :
    ⦃⌜True⌝⦄
    numpy_where condition x y
    ⦃⇓result => ⌜∀ i : Fin n, 
      (condition.get i = true → result.get i = x.get i) ∧
      (condition.get i = false → result.get i = y.get i)⌝⦄ := by
  simp [numpy_where]
  intro i
  simp [Vector.get_zipWith3]
  cases h : condition.get i with
  | true => simp [select_element, h]
  | false => simp [select_element, h]