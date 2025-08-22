namespace NpSum

def sum {n : Nat} (a : Vector Int n) : Int := 
  a.toList.foldl (· + ·) 0

-- LLM HELPER
lemma vector_get_add_bound {n : Nat} (a : Vector Int n) (start i : Nat) (h1 : start + i < n) : 
  start + i < a.size := by
  simp [Vector.size_val]
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
        simp [Vector.size_val]
        exact Nat.lt_of_succ_le (Nat.succ_le_of_lt (Nat.lt_of_lt_of_le (Nat.zero_lt_succ _) (Nat.le_refl _)))
      have h4 : start + i < finish := Nat.add_lt_of_le_of_lt (Nat.le_refl _) h3
      exact Nat.lt_of_lt_of_le h4 h2
    )) 0
  else 0

-- LLM HELPER
lemma sum_eq_sumArray_aux {n : Nat} (a : Vector Int n) :
  a.toList.foldl (· + ·) 0 = (List.range n).foldl (fun acc i => acc + a[i]'(by simp [Vector.size_val])) 0 := by
  simp [Vector.size_val]
  congr
  ext acc i
  congr

-- LLM HELPER
lemma sumArray_spec_aux {n : Nat} (a : Vector Int n) (start finish : Nat) (h1 : start ≤ finish) (h2 : finish ≤ n) :
  sumArray a start finish = (List.range (finish - start)).foldl (fun acc i => acc + a[start + i]'(by
    have h3 : i < finish - start := by
      simp [Vector.size_val]
      exact Nat.lt_of_succ_le (Nat.succ_le_of_lt (Nat.lt_of_lt_of_le (Nat.zero_lt_succ _) (Nat.le_refl _)))
    have h4 : start + i < finish := Nat.add_lt_of_le_of_lt (Nat.le_refl _) h3
    exact Nat.lt_of_lt_of_le h4 h2
  )) 0 := by
  simp [sumArray]
  split
  · rfl
  · contradiction

-- LLM HELPER  
lemma sum_append_aux {m n : Nat} (a : Vector Int m) (b : Vector Int n) :
  (a ++ b).toList.foldl (· + ·) 0 = a.toList.foldl (· + ·) 0 + b.toList.foldl (· + ·) 0 := by
  rw [Vector.append_val]
  rw [List.foldl_append]
  simp [List.foldl_add]

theorem sum_spec {n : Nat} (a : Vector Int n) :
  sum a = sumArray a 0 n ∧
  ∀ start finish : Nat, start ≤ finish → finish ≤ n → 
    sumArray a start finish = (List.range (finish - start)).foldl (fun acc i => acc + a[start + i]'(by
      have h3 : i < finish - start := by
        simp [Vector.size_val]
        exact Nat.lt_of_succ_le (Nat.succ_le_of_lt (Nat.lt_of_lt_of_le (Nat.zero_lt_succ _) (Nat.le_refl _)))
      have h4 : start + i < finish := Nat.add_lt_of_le_of_lt (Nat.le_refl _) h3
      exact Nat.lt_of_lt_of_le h4 finish_le_n
    )) 0 ∧
  ∀ m n : Nat, ∀ a : Vector Int m, ∀ b : Vector Int n, sum (a ++ b) = sum a + sum b := by
  constructor
  · simp [sum, sumArray]
    split
    · simp [Nat.sub_zero]
      exact sum_eq_sumArray_aux a
    · simp at *
  · constructor
    · intros start finish h1 h2
      exact sumArray_spec_aux a start finish h1 h2
    · intros m n a b
      simp [sum]
      exact sum_append_aux a b

end NpSum