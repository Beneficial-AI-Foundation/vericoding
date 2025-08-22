namespace NpCountnonzero

def nonzero {n : Nat} (arr : Vector Float n) : Nat := 
  arr.toList.filter (fun x => x ≠ 0.0) |>.length

-- LLM HELPER
lemma filter_length_nonneg (l : List Float) : (l.filter (fun x => x ≠ 0.0)).length ≥ 0 := by
  simp [List.length_nonneg]

-- LLM HELPER
lemma vector_head_tail_property {n : Nat} (arr : Vector Float (n + 1)) (h : arr[0]! = 0.0) :
  arr.toList.filter (fun x => x ≠ 0.0) = arr.tail.toList.filter (fun x => x ≠ 0.0) := by
  have head_eq : arr.toList.head! = 0.0 := by
    rw [Vector.getElem_toList]
    exact h
  have arr_cons : arr.toList = arr.toList.head! :: arr.toList.tail := by
    apply List.cons_head_tail
    simp [Vector.toList_length]
  have tail_eq : arr.toList.tail = arr.tail.toList := by
    rw [Vector.toList_tail]
  rw [arr_cons, head_eq, tail_eq]
  simp [List.filter_cons, if_neg]
  norm_num

theorem nonzero_spec {n : Nat} (arr : Vector Float n) :
  let num := nonzero arr
  (num ≥ 0) ∧
  (n > 0 → arr[0]! = 0.0 → nonzero (arr.tail) = num - 1) := by
  constructor
  · exact filter_length_nonneg arr.toList
  · intro hn h_zero
    cases' n with n
    · contradiction
    · unfold nonzero
      rw [vector_head_tail_property arr h_zero]
      simp [Nat.add_sub_cancel]

end NpCountnonzero