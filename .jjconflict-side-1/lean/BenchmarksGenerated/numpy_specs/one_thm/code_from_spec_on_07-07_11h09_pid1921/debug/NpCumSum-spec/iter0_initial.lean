namespace NpCumSum

def cumSum {n : Nat} (a : Vector Int n) : Vector Int n := 
  match n with
  | 0 => Vector.nil
  | m + 1 => 
    let rec cumSumAux (k : Nat) (acc : Int) : k ≤ m + 1 → Vector Int k
      | 0, _ => Vector.nil
      | j + 1, h => 
        let newAcc := acc + a[j]'(by omega)
        Vector.cons newAcc (cumSumAux j acc (by omega))
    cumSumAux (m + 1) 0 (by omega)

-- LLM HELPER
lemma cumSum_length {n : Nat} (a : Vector Int n) : (cumSum a).length = n := by
  simp [cumSum]
  split
  · simp [Vector.length_nil]
  · simp [Vector.length_cons]
    sorry

-- LLM HELPER  
lemma cumSum_get_zero {n : Nat} (a : Vector Int n) (h : n > 0) : 
  (cumSum a)[0]'(by omega) = a[0]'(by omega) := by
  simp [cumSum]
  split
  · omega
  · simp [Vector.get_cons_zero]
    sorry

-- LLM HELPER
lemma cumSum_get_succ {n : Nat} (a : Vector Int n) (i : Fin n) (h : i.val > 0) :
  (cumSum a)[i] = (cumSum a)[i.val - 1]'(by omega) + a[i] := by
  simp [cumSum]
  split
  · have : i.val < 0 := by omega
    omega
  · sorry

theorem cumSum_spec {n : Nat} (a : Vector Int n) :
  (cumSum a)[0]'(by omega) = a[0]'(by omega) ∧
  ∀ i : Fin n, i.val > 0 → (cumSum a)[i] = (cumSum a)[i.val - 1]'(by omega) + a[i] := by
  constructor
  · cases' n with n
    · have : (0 : Nat) < 0 := by omega
      exact False.elim this
    · exact cumSum_get_zero a (by omega)
  · intro i h
    exact cumSum_get_succ a i h

end NpCumSum