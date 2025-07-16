namespace NpSum

def sum {n : Nat} (a : Vector Int n) : Int := 
  a.toList.foldl (· + ·) 0

def sumArray {n : Nat} (a : Vector Int n) (start finish : Nat) : Int := 
  if start ≥ finish ∨ finish > n then 0
  else (List.range (finish - start)).foldl (fun acc i => acc + a[start + i]'(by omega)) 0

/- LLM HELPER -/
lemma sum_eq_sumArray {n : Nat} (a : Vector Int n) :
  sum a = sumArray a 0 n := by
  simp [sum, sumArray]
  rw [if_neg]
  · simp [Vector.toList_eq_map_range]
    congr 1
    ext i
    simp
  · simp

/- LLM HELPER -/
lemma sumArray_spec {n : Nat} (a : Vector Int n) (start finish : Nat) 
  (h1 : start ≤ finish) (h2 : finish ≤ n) :
  sumArray a start finish = (List.range (finish - start)).foldl (fun acc i => acc + a[start + i]'(by omega)) 0 := by
  simp [sumArray]
  rw [if_neg]
  simp [h1, h2]

/- LLM HELPER -/
lemma sum_append {m n : Nat} (a : Vector Int m) (b : Vector Int n) :
  sum (a ++ b) = sum a + sum b := by
  simp [sum, Vector.toList_append]
  rw [List.foldl_append]
  simp [List.foldl_add_zero]

/- LLM HELPER -/
lemma List.foldl_add_zero {l : List Int} : 
  l.foldl (· + ·) 0 = l.foldl (· + ·) 0 + 0 := by simp

theorem sum_spec {n : Nat} (a : Vector Int n) :
  sum a = sumArray a 0 n ∧
  ∀ start finish : Nat, start ≤ finish → finish ≤ n → 
    sumArray a start finish = (List.range (finish - start)).foldl (fun acc i => acc + a[start + i]'(by omega)) 0 ∧
  ∀ m n : Nat, ∀ a : Vector Int m, ∀ b : Vector Int n, sum (a ++ b) = sum a + sum b := by
  constructor
  · exact sum_eq_sumArray a
  constructor
  · intros start finish h1 h2
    exact sumArray_spec a start finish h1 h2
  · intros m n a b
    exact sum_append a b

end NpSum