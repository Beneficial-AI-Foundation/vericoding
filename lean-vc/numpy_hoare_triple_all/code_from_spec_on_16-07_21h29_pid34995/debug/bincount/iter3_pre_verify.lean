import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

-- LLM HELPER
def count_occurrences (x : List Nat) (val : Nat) : Nat :=
  x.filter (· = val) |>.length

-- LLM HELPER
def build_bincount_aux (x : List Nat) (max_val : Nat) : Nat → Nat
  | val => count_occurrences x val

-- LLM HELPER
def build_bincount_vector (x : List Nat) (max_val : Nat) : Vector Nat (max_val + 1) :=
  Vector.ofFn (fun i : Fin (max_val + 1) => count_occurrences x i.val)

/-- numpy.bincount: Count number of occurrences of each value in array of non-negative ints.

    Count number of occurrences of each value in array of non-negative ints.
    The number of bins (of size 1) is one larger than the largest value in x.
    Each bin gives the number of occurrences of its index value in x.
    
    This function takes a 1D array of non-negative integers and returns
    an array where the i-th element is the count of how many times the
    value i appears in the input array.
-/
def numpy_bincount {n : Nat} (x : Vector Nat n) (max_val : Nat) 
    (h_bounds : ∀ i : Fin n, x.get i ≤ max_val) : Id (Vector Nat (max_val + 1)) :=
  build_bincount_vector x.toList max_val

-- LLM HELPER
lemma vector_get_ofFn {n : Nat} (f : Fin n → α) (i : Fin n) : 
  (Vector.ofFn f).get i = f i := by
  simp [Vector.get, Vector.ofFn]

/-- Specification: numpy.bincount returns count of occurrences of each value.

    Precondition: All values in x are non-negative and ≤ max_val
    Postcondition: result[i] = count of occurrences of value i in x
-/
theorem numpy_bincount_spec {n : Nat} (x : Vector Nat n) (max_val : Nat) 
    (h_bounds : ∀ i : Fin n, x.get i ≤ max_val) :
    ⦃⌜∀ i : Fin n, x.get i ≤ max_val⌝⦄
    numpy_bincount x max_val h_bounds
    ⦃⇓result => ⌜∀ val : Fin (max_val + 1), 
                   result.get val = (x.toList.filter (· = val.val)).length⌝⦄ := by
  unfold numpy_bincount
  simp [build_bincount_vector, count_occurrences]
  intro val
  rw [vector_get_ofFn]
  rfl