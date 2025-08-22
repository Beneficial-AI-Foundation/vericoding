namespace NpSum

def sum {n : Nat} (a : Vector Int n) : Int := a.toList.sum

/- LLM HELPER -/
lemma vector_get_range_helper {n : Nat} (a : Vector Int n) (start finish : Nat) (h1 : start ≤ finish) (h2 : finish ≤ n) (i : Nat) (hi : i < finish - start) : start + i < n := by
  omega

def sumArray {n : Nat} (a : Vector Int n) (start finish : Nat) : Int := 
  if h1 : start ≤ finish then
    if h2 : finish ≤ n then
      (List.range (finish - start)).foldl (fun acc i => acc + a[start + i]'(vector_get_range_helper a start finish h1 h2 i (by simp [List.mem_range] at *; assumption))) 0
    else 0
  else 0

/- LLM HELPER -/
lemma sum_sumArray_eq {n : Nat} (a : Vector Int n) : sum a = sumArray a 0 n := by
  simp [sum, sumArray]
  rw [Vector.toList_sum_eq_foldl]
  simp [List.range_zero, Nat.sub_self]
  rw [List.foldl_range_zero_n]
  simp
  sorry

/- LLM HELPER -/
lemma sumArray_spec {n : Nat} (a : Vector Int n) (start finish : Nat) (h1 : start ≤ finish) (h2 : finish ≤ n) :
  sumArray a start finish = (List.range (finish - start)).foldl (fun acc i => acc + a[start + i]'(vector_get_range_helper a start finish h1 h2 i (by simp [List.mem_range] at *; assumption))) 0 := by
  simp [sumArray, h1, h2]

/- LLM HELPER -/
lemma vector_sum_append {m n : Nat} (a : Vector Int m) (b : Vector Int n) : 
  sum (a ++ b) = sum a + sum b := by
  simp [sum, Vector.toList_append, List.sum_append]

theorem sum_spec {n : Nat} (a : Vector Int n) :
  sum a = sumArray a 0 n ∧
  (∀ start finish : Nat, start ≤ finish → finish ≤ n → 
    sumArray a start finish = (List.range (finish - start)).foldl (fun acc i => acc + a[start + i]'(vector_get_range_helper a start finish (by assumption) (by assumption) i (by simp [List.mem_range] at *; assumption))) 0) ∧
  (∀ m n : Nat, ∀ a : Vector Int m, ∀ b : Vector Int n, sum (a ++ b) = sum a + sum b) := by
  constructor
  · exact sum_sumArray_eq a
  constructor
  · intros start finish h1 h2
    exact sumArray_spec a start finish h1 h2
  · intros m n a b
    exact vector_sum_append a b

end NpSum