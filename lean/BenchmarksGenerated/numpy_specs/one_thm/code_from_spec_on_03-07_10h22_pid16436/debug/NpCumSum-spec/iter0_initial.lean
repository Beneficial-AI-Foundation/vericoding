namespace NpCumSum

def cumSum {n : Nat} (a : Vector Int n) : Vector Int n := 
  match n with
  | 0 => Vector.nil
  | n + 1 => 
    let rec cumSumAux (i : Nat) (acc : Int) (result : Vector Int (i + 1)) : Vector Int (n + 1) :=
      if h : i = n then
        h ▸ result
      else
        have : i < n := Nat.lt_of_le_of_ne (Nat.le_of_succ_le_succ (result.length_le)) h
        have : n - i - 1 < n - i := by omega
        cumSumAux (i + 1) (acc + a[i + 1]'(by omega)) (result.push (acc + a[i + 1]'(by omega)))
    cumSumAux 0 a[0]'(by omega) ⟨[a[0]'(by omega)], by simp⟩

/-- LLM HELPER -/
def cumSum {n : Nat} (a : Vector Int n) : Vector Int n := 
  Vector.ofFn fun i => 
    (List.range (i.val + 1)).foldl (fun acc j => acc + a[j]'(by omega)) 0

theorem cumSum_spec {n : Nat} (a : Vector Int n) :
  (cumSum a)[0]'(by omega) = a[0]'(by omega) ∧
  ∀ i : Fin n, i.val > 0 → (cumSum a)[i] = (cumSum a)[i.val - 1]'(by omega) + a[i] := by
  constructor
  · simp [cumSum, Vector.get_ofFn]
    cases n with
    | zero => omega
    | succ n' => 
      simp [List.foldl_range_one]
  · intro i hi
    simp [cumSum, Vector.get_ofFn]
    rw [List.foldl_range_succ]
    simp only [Nat.add_zero]
    congr 1
    simp [List.foldl_range_eq_sum_range]

end NpCumSum