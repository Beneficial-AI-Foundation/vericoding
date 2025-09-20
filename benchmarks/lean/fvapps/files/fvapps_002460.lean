-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Array.shape (a : Array (Array α)) : Nat × Nat :=
  sorry

def concatenate_arrays {α : Type} (n m p : Nat) (array1 array2 : Array (Array α)) :
  Array (Array α) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem concatenate_arrays_shape (n m p : Nat) (array1 array2 : Array (Array α)) :
  (concatenate_arrays n m p array1 array2).shape = (n + m, p) :=
sorry

theorem concatenate_arrays_preserves_first (n m p : Nat) (array1 array2 : Array (Array α)) :
  ∀ i < n, (concatenate_arrays n m p array1 array2)[i]! = array1[i]! :=
sorry

theorem concatenate_arrays_preserves_second (n m p : Nat) (array1 array2 : Array (Array α)) :
  ∀ i < m, (concatenate_arrays n m p array1 array2)[n + i]! = array2[i]! :=
sorry

theorem concatenate_arrays_singleton (n p : Nat) (value : α)
  (array1 : Array (Array α)) (array2 : Array (Array α)) :
  array2.size = 1 →
  (∀ i < n, (array1[i]!).size = p) →
  (array2[0]!).size = p →
  (concatenate_arrays n 1 p array1 array2).shape = (n + 1, p) :=
sorry
-- </vc-theorems>