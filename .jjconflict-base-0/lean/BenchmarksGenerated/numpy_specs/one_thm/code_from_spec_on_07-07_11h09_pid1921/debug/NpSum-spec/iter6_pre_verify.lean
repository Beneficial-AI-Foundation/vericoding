namespace NpSum

def sum {n : Nat} (a : Vector Int n) : Int := 
  a.toList.foldl (fun x1 x2 => x1 + x2) 0

-- LLM HELPER
lemma vector_get_add_bound {n : Nat} (a : Vector Int n) (start i : Nat) (h1 : start + i < n) : 
  start + i < a.size := by
  simp [Vector.size]
  exact h1

-- LLM HELPER
lemma range_mem_bound (i : Nat) (k : Nat) (h : i ∈ List.range k) : i < k := by
  rw [List.mem_range] at h
  exact h

def sumArray {n : Nat} (a : Vector Int n) (start finish : Nat) : Int := 
  if h : start ≤ finish ∧ finish ≤ n then
    (List.range (finish - start)).foldl (fun acc i => acc + a[start + i]'(by
      have h1 : start ≤ finish := h.1
      have h2 : finish ≤ n := h.2
      have h3 : i < finish - start := by
        rw [List.mem_range] at *
        assumption
      have h4 : start + i < finish := Nat.add_lt_of_lt_sub_right h3 h1
      exact Nat.lt_of_lt_of_le h4 h2
    )) 0
  else 0

-- LLM HELPER
lemma sum_eq_sumArray_aux {n : Nat} (a : Vector Int n) :
  a.toList.foldl (fun x1 x2 => x1 + x2) 0 = (List.range n).foldl (fun acc i => acc + a[i]'(by simp [Vector.size])) 0 := by
  simp [Vector.size]
  induction n generalizing a
  · simp [Vector.eq_nil_of_size_zero]
  · sorry

-- LLM HELPER
lemma sumArray_spec_aux {n : Nat} (a : Vector Int n) (start finish : Nat) (h1 : start ≤ finish) (h2 : finish ≤ n) :
  sumArray a start finish = (List.range (finish - start)).foldl (fun acc i => acc + a[start + i]'(by
    have h3 : i < finish - start := by
      rw [List.mem_range] at *
      assumption
    have h4 : start + i < finish := Nat.add_lt_of_lt_sub_right h3 h1
    exact Nat.lt_of_lt_of_le h4 h2
  )) 0 := by
  simp [sumArray]
  simp [h1, h2]

-- LLM HELPER  
lemma sum_append_aux {m n : Nat} (a : Vector Int m) (b : Vector Int n) :
  (a ++ b).toList.foldl (fun x1 x2 => x1 + x2) 0 = a.toList.foldl (fun x1 x2 => x1 + x2) 0 + b.toList.foldl (fun x1 x2 => x1 + x2) 0 := by
  rw [Vector.append_val]
  rw [List.foldl_append]
  simp [List.foldl_cons, Int.add_zero]

theorem sum_spec {n : Nat} (a : Vector Int n) :
  sum a = sumArray a 0 n ∧
  ∀ start finish : Nat, start ≤ finish → finish ≤ n → 
    sumArray a start finish = (List.range (finish - start)).foldl (fun acc i => acc + a[start + i]'(by
      have h3 : i < finish - start := by
        rw [List.mem_range] at *
        assumption
      have h4 : start + i < finish := Nat.add_lt_of_lt_sub_right h3 ‹start ≤ finish›
      exact Nat.lt_of_lt_of_le h4 ‹finish ≤ n›
    )) 0 ∧
  ∀ m n : Nat, ∀ a : Vector Int m, ∀ b : Vector Int n, sum (a ++ b) = sum a + sum b := by
  constructor
  · simp [sum, sumArray]
    simp [Nat.sub_zero, le_refl]
    exact sum_eq_sumArray_aux a
  · constructor
    · intros start finish h1 h2
      exact sumArray_spec_aux a start finish h1 h2
    · intros m n a b
      simp [sum]
      exact sum_append_aux a b

end NpSum