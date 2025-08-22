namespace NpPolyder

-- LLM HELPER
def polyder_aux (coeffs : List Float) (m : Int) : List Float :=
  if m ≤ 0 then coeffs
  else
    match coeffs with
    | [] => []
    | [_] => []
    | _ :: tail => polyder_aux (List.zipWith (· * ·) tail (List.range tail.length |>.map (fun i => Float.ofNat (i + 1)))) (m - 1)
termination_by m.natAbs

def polyder {n : Nat} (poly : Vector Float n) (m : Int) : Vector Float (n - m.natAbs) := 
  let result_list := polyder_aux poly.toList m
  let target_length := n - m.natAbs
  let padded_list := if result_list.length < target_length then 
    result_list ++ List.replicate (target_length - result_list.length) 0.0
  else 
    result_list.take target_length
  ⟨padded_list, by
    simp [padded_list, target_length]
    split_ifs with h1
    · simp [List.length_append, List.length_replicate]
    · simp [List.length_take, Nat.min_def]
      split_ifs with h2
      · omega
      · rfl⟩

-- LLM HELPER
lemma vector_mk_length (l : List Float) (h : l.length = n) : (⟨l, h⟩ : Vector Float n).toList.length = n := by
  simp [Vector.toList]

theorem polyder_spec {n : Nat} (poly : Vector Float n) (m : Int)
  (h : m > 0) :
  let ret := polyder poly m
  ret.toList.length = n - m.natAbs := by
  simp [polyder, Vector.toList]
  split_ifs with h1
  · simp [List.length_append, List.length_replicate]
  · simp [List.length_take, Nat.min_def]
    split_ifs with h2
    · omega
    · rfl

end NpPolyder