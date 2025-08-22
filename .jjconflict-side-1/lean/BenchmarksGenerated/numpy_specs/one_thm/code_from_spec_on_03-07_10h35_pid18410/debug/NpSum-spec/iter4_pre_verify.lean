namespace NpSum

def sum {n : Nat} (a : Vector Int n) : Int := 
  a.toList.foldl (· + ·) 0

def sumArray {n : Nat} (a : Vector Int n) (start finish : Nat) : Int := 
  List.foldl (fun acc i => if h : start + i < n then acc + a[start + i] else acc) 0 (List.range (finish - start))

/- LLM HELPER -/
lemma sumArray_zero_n {n : Nat} (a : Vector Int n) :
  sumArray a 0 n = sum a := by
  simp [sum, sumArray]
  induction' n with n ih
  · simp
  · simp [List.range_succ]
    congr 1
    ext acc i
    simp
    rw [Nat.zero_add]

/- LLM HELPER -/
lemma sumArray_correct {n : Nat} (a : Vector Int n) (start finish : Nat) 
  (h1 : start ≤ finish) (h2 : finish ≤ n) :
  sumArray a start finish = List.foldl (fun acc i => 
    acc + a[start + i]'(by 
      have : i < finish - start := by
        apply List.mem_range.mp
        assumption
      linarith [h2])) 0 (List.range (finish - start)) := by
  simp [sumArray]
  congr 2
  ext acc i
  simp
  have h : start + i < n := by
    have : i < finish - start := by
      apply List.mem_range.mp
      assumption
    linarith [h2]
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
    sumArray a start finish = List.foldl (fun acc i => acc + a[start + i]'(by 
      have : i < finish - start := by
        apply List.mem_range.mp
        assumption
      linarith)) 0 (List.range (finish - start)) ∧
  ∀ m n : Nat, ∀ a : Vector Int m, ∀ b : Vector Int n, sum (a ++ b) = sum a + sum b := by
  exact ⟨sumArray_zero_n a, fun start finish h1 h2 => sumArray_correct a start finish h1 h2, fun m n a b => sum_append a b⟩

end NpSum