namespace NpCumSum

def cumSum {n : Nat} (a : Vector Int n) : Vector Int n := 
  Vector.ofFn fun i => 
    (List.range (i.val + 1)).foldl (fun acc j => acc + a[j]!) 0

/-- LLM HELPER -/
lemma List.foldl_range_zero (f : Int → Nat → Int) (init : Int) :
  List.foldl f init (List.range 1) = f init 0 := by
  simp [List.range, List.foldl]

/-- LLM HELPER -/
lemma List.foldl_range_succ (f : Int → Nat → Int) (init : Int) (n : Nat) :
  List.foldl f init (List.range (n + 1)) = 
  f (List.foldl f init (List.range n)) n := by
  simp [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- LLM HELPER -/
lemma Vector.get_ofFn {α : Type*} {n : Nat} (f : Fin n → α) (i : Fin n) :
  (Vector.ofFn f)[i] = f i := by
  simp [Vector.get_eq_get, Vector.toList_ofFn, List.get_ofFn]

theorem cumSum_spec {n : Nat} (a : Vector Int n) :
  (n > 0 → (cumSum a)[⟨0, by {cases n; contradiction; exact Nat.zero_lt_succ _}⟩] = a[⟨0, by {cases n; contradiction; exact Nat.zero_lt_succ _}⟩]) ∧
  ∀ i : Fin n, i.val > 0 → (cumSum a)[i] = (cumSum a)[⟨i.val - 1, by
    have h1 : i.val > 0 := by assumption
    have h2 : i.val - 1 < i.val := Nat.sub_lt i.isLt (Nat.zero_lt_of_ne_zero (ne_of_gt h1))
    have h3 : i.val < n := i.isLt  
    exact Nat.lt_trans h2 h3⟩] + a[i] := by
  constructor
  · intro hn
    cases n with
    | zero => contradiction
    | succ n' => 
      simp [cumSum]
      rw [Vector.get_ofFn]
      simp [List.foldl_range_zero]
  · intro i hi
    simp [cumSum]
    rw [Vector.get_ofFn, Vector.get_ofFn]
    rw [List.foldl_range_succ]
    simp only [Nat.add_zero]
    congr 1

end NpCumSum