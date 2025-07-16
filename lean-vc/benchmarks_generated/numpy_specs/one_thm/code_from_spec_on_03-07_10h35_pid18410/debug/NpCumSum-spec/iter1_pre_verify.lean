namespace NpCumSum

def cumSum {n : Nat} (a : Vector Int n) : Vector Int n := 
  Vector.ofFn (fun i => (List.range (i.val + 1)).foldl (fun acc j => acc + a[j]'(by omega)) 0)

theorem cumSum_spec {n : Nat} (a : Vector Int n) :
  (cumSum a)[0]'(by omega) = a[0]'(by omega) ∧
  ∀ i : Fin n, i.val > 0 → (cumSum a)[i] = (cumSum a)[i.val - 1]'(by omega) + a[i] := by
  constructor
  · -- First part: (cumSum a)[0] = a[0]
    simp [cumSum]
    rfl
  · -- Second part: recurrence relation
    intro i hi
    simp [cumSum]
    have h_range : List.range (i.val + 1) = List.range i.val ++ [i.val] := by
      rw [List.range_succ]
    rw [h_range]
    rw [List.foldl_append]
    simp [List.foldl_cons, List.foldl_nil]
    ring