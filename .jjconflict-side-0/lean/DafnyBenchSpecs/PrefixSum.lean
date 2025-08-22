import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- Sum of array elements from index i to j (exclusive).
    This is a specification function used to define correctness. -/
def sum (a : Array Int) (i j : Nat) : Int :=
  if h : i < j ∧ j ≤ a.size then
    let rec loop (k : Nat) (acc : Int) : Int :=
      if k = j then acc
      else if h' : k < a.size then loop (k + 1) (acc + a[k])
      else acc
    loop i 0
  else 0

/-- Query method that computes the sum of array elements from index i to j.
    
    Preconditions:
    - 0 ≤ i ≤ j ≤ a.size
    
    Postconditions:
    - Returns sum(a, i, j)
-/
def query (a : Array Int) (i j : Nat) : Id Int := do
  sorry -- Implementation left as exercise

theorem query_spec (a : Array Int) (i j : Nat) 
    (h_bounds : 0 ≤ i ∧ i ≤ j ∧ j ≤ a.size) :
    ⦃⌜True⌝⦄
    query a i j
    ⦃⇓result => ⌜result = sum a i j⌝⦄ := by
  mvcgen [query]
  sorry

/-- Predicate that checks if c is a valid prefix sum array for a -/
def is_prefix_sum_for (a c : Array Int) : Prop :=
  a.size + 1 = c.size ∧
  c[0]! = 0 ∧
  ∀ j : Nat, 1 ≤ j ∧ j ≤ a.size → c[j]! = sum a 0 j

/-- Fast query using precomputed prefix sums.
    
    Preconditions:
    - c is a valid prefix sum array for a
    - 0 ≤ i ≤ j ≤ a.size < c.size
    
    Postconditions:
    - Returns sum(a, i, j)
-/
def queryFast (a c : Array Int) (i j : Nat) : Id Int := do
  sorry -- Implementation left as exercise

theorem queryFast_spec (a c : Array Int) (i j : Nat)
    (h_prefix : is_prefix_sum_for a c)
    (h_bounds : 0 ≤ i ∧ i ≤ j ∧ j ≤ a.size ∧ a.size < c.size) :
    ⦃⌜True⌝⦄
    queryFast a c i j
    ⦃⇓result => ⌜result = sum a i j⌝⦄ := by
  mvcgen [queryFast]
  sorry

/-- Custom list type (mirroring Dafny's datatype) -/
inductive MyList (α : Type)
  | Nil : MyList α
  | Cons : α → MyList α → MyList α

/-- Membership predicate for custom list -/
def mem {α : Type} [DecidableEq α] (x : α) : MyList α → Bool
  | MyList.Nil => false
  | MyList.Cons y r => if x = y then true else mem x r

/-- Convert array to custom list ensuring all elements are preserved.
    
    Preconditions:
    - a.size > 0
    
    Postconditions:
    - All elements of the array are members of the returned list
-/
def from_array (α : Type) [DecidableEq α] (a : Array α) : Id (MyList α) := do
  sorry -- Implementation left as exercise

theorem from_array_spec (α : Type) [DecidableEq α] [Inhabited α] (a : Array α)
    (h_size : a.size > 0) :
    ⦃⌜True⌝⦄
    from_array α a
    ⦃⇓result => ⌜∀ j : Nat, 0 ≤ j ∧ j < a.size → mem a[j]! result = true⌝⦄ := by
  mvcgen [from_array]
  sorry