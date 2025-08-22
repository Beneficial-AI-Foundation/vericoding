namespace NpSum

def sum {n : Nat} (a : Vector Int n) : Int := 
  List.foldl (fun acc x => acc + x) 0 a.toList

-- LLM HELPER
lemma vector_get_add_bound {n : Nat} (a : Vector Int n) (start i : Nat) (h1 : start + i < n) : 
  start + i < a.size := by
  simp [Vector.size]
  exact h1

-- LLM HELPER
lemma range_mem_bound (i : Nat) (k : Nat) (h : i ∈ List.range k) : i < k := by
  rw [List.mem_range] at h
  exact h

-- LLM HELPER
lemma nat_add_lt_of_lt_sub {a b c : Nat} (h1 : c < b - a) (h2 : a ≤ b) : a + c < b := by
  have h3 : a + c < a + (b - a) := by
    rw [Nat.add_lt_add_iff_left]
    exact h1
  rw [Nat.add_sub_cancel' h2] at h3
  exact h3

def sumArray {n : Nat} (a : Vector Int n) (start finish : Nat) : Int := 
  if h : start ≤ finish ∧ finish ≤ n then
    List.foldl (fun acc i => 
      have h1 : start ≤ finish := h.1
      have h2 : finish ≤ n := h.2
      have h3 : i < finish - start := range_mem_bound i (finish - start) (by assumption)
      have h4 : start + i < finish := nat_add_lt_of_lt_sub h3 h1
      acc + a[start + i]'(Nat.lt_of_lt_of_le h4 h2)
    ) 0 (List.range (finish - start))
  else 0

-- LLM HELPER
lemma sum_eq_sumArray_aux {n : Nat} (a : Vector Int n) :
  List.foldl (fun acc x => acc + x) 0 a.toList = List.foldl (fun acc i => acc + a[i]'(by simp [Vector.size])) 0 (List.range n) := by
  simp [Vector.size]
  induction n generalizing a
  · simp [Vector.eq_nil_of_size_zero]
  · case succ n ih =>
    have h : a = Vector.cons (a.head) (a.tail) := by
      simp [Vector.cons_head_tail]
    rw [h]
    simp [Vector.toList_cons, List.foldl_cons, List.range_succ, List.foldl_append]
    rw [ih]
    simp [List.foldl_map]
    congr

-- LLM HELPER
lemma sumArray_spec_aux {n : Nat} (a : Vector Int n) (start finish : Nat) (h1 : start ≤ finish) (h2 : finish ≤ n) :
  sumArray a start finish = List.foldl (fun acc i => 
    have h3 : i < finish - start := range_mem_bound i (finish - start) (by assumption)
    have h4 : start + i < finish := nat_add_lt_of_lt_sub h3 h1
    acc + a[start + i]'(Nat.lt_of_lt_of_le h4 h2)
  ) 0 (List.range (finish - start)) := by
  rw [sumArray]
  simp [h1, h2]

-- LLM HELPER  
lemma sum_append_aux {m n : Nat} (a : Vector Int m) (b : Vector Int n) :
  List.foldl (fun acc x => acc + x) 0 (a ++ b).toList = List.foldl (fun acc x => acc + x) 0 a.toList + List.foldl (fun acc x => acc + x) 0 b.toList := by
  rw [Vector.append_val]
  rw [List.foldl_append]
  simp [List.foldl_cons, Int.add_zero]

theorem sum_spec {n : Nat} (a : Vector Int n) :
  sum a = sumArray a 0 n ∧
  ∀ start finish : Nat, start ≤ finish → finish ≤ n → 
    sumArray a start finish = List.foldl (fun acc i => 
      have h3 : i < finish - start := range_mem_bound i (finish - start) (by assumption)
      have h4 : start + i < finish := nat_add_lt_of_lt_sub h3 ‹start ≤ finish›
      acc + a[start + i]'(Nat.lt_of_lt_of_le h4 ‹finish ≤ n›)
    ) 0 (List.range (finish - start)) ∧
  ∀ m n : Nat, ∀ a : Vector Int m, ∀ b : Vector Int n, sum (a ++ b) = sum a + sum b := by
  constructor
  · rw [sum, sumArray]
    simp [Nat.sub_zero, Nat.le_refl]
    exact sum_eq_sumArray_aux a
  · constructor
    · intros start finish h1 h2
      exact sumArray_spec_aux a start finish h1 h2
    · intros m n a b
      rw [sum]
      exact sum_append_aux a b

end NpSum