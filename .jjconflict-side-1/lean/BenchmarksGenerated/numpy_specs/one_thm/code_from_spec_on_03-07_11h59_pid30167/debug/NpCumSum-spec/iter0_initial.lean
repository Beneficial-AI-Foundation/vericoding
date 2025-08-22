namespace NpCumSum

def cumSum {n : Nat} (a : Vector Int n) : Vector Int n := 
  Vector.ofFn (fun i => (List.range (i.val + 1)).map (fun j => a[j]'(by omega)) |>.sum)

theorem cumSum_spec {n : Nat} (a : Vector Int n) :
  (cumSum a)[0]'(by omega) = a[0]'(by omega) ∧
  ∀ i : Fin n, i.val > 0 → (cumSum a)[i] = (cumSum a)[i.val - 1]'(by omega) + a[i] := by
  constructor
  · simp [cumSum, Vector.get_ofFn]
    simp [List.range, List.map, List.sum]
  · intro i hi
    simp [cumSum, Vector.get_ofFn]
    have h1 : List.range (i.val + 1) = List.range i.val ++ [i.val] := by
      rw [List.range_succ_eq_map]
      simp [List.range_concat]
    rw [h1]
    simp [List.map_append, List.sum_append]
    ring

end NpCumSum