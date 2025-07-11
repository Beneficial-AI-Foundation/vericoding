namespace NpSum

def sum {n : Nat} (a : Vector Int n) : Int := 
  a.toList.foldl (· + ·) 0

def sumArray {n : Nat} (a : Vector Int n) (start finish : Nat) : Int := 
  (List.range (finish - start)).foldl (fun acc i => 
    if h : start + i < n then acc + a[start + i] else acc) 0

/- LLM HELPER -/
lemma sumArray_zero_n {n : Nat} (a : Vector Int n) :
  sumArray a 0 n = sum a := by
  simp [sum, sumArray]
  have h : ∀ i ∈ List.range n, 0 + i < n := by
    intro i hi
    simp at hi
    exact hi
  congr 1
  ext i
  simp [h]

/- LLM HELPER -/
lemma sumArray_correct {n : Nat} (a : Vector Int n) (start finish : Nat) 
  (h1 : start ≤ finish) (h2 : finish ≤ n) :
  sumArray a start finish = (List.range (finish - start)).foldl (fun acc i => 
    acc + a[start + i]'(by omega)) 0 := by
  simp [sumArray]
  congr 1
  ext acc i
  simp
  have h : start + i < n := by omega
  simp [h]

/- LLM HELPER -/
lemma sum_append {m n : Nat} (a : Vector Int m) (b : Vector Int n) :
  sum (a ++ b) = sum a + sum b := by
  simp [sum]
  rw [Vector.toList_append]
  rw [List.foldl_append]

theorem sum_spec {n : Nat} (a : Vector Int n) :
  sum a = sumArray a 0 n ∧
  ∀ start finish : Nat, start ≤ finish → finish ≤ n → 
    sumArray a start finish = (List.range (finish - start)).foldl (fun acc i => acc + a[start + i]'(by omega)) 0 ∧
  ∀ m n : Nat, ∀ a : Vector Int m, ∀ b : Vector Int n, sum (a ++ b) = sum a + sum b := by
  constructor
  · exact sumArray_zero_n a
  constructor
  · intro start finish h1 h2
    exact sumArray_correct a start finish h1 h2
  · intro m n a b
    exact sum_append a b

end NpSum