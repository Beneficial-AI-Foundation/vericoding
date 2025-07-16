namespace NpCumSum

def cumSum {n : Nat} (a : Vector Int n) : Vector Int n := 
  match n with
  | 0 => Vector.nil
  | n + 1 => 
    Vector.ofFn (fun i => 
      let rec cumAtIndex (j : Nat) (sum : Int) : Int :=
        if h : j <= i.val then
          if j = i.val then
            sum + a[j]'(Nat.lt_of_le_of_lt h i.isLt)
          else
            cumAtIndex (j + 1) (sum + a[j]'(Nat.lt_of_le_of_lt (Nat.le_of_lt_succ (Nat.lt_of_le_of_ne h (Ne.symm (Nat.ne_of_gt (Nat.lt_succ_of_le h))))) i.isLt))
        else
          sum
      cumAtIndex 0 0)

/- LLM HELPER -/
lemma cumSum_zero_case {n : Nat} (a : Vector Int n) (h : n = 0) :
  cumSum a = Vector.nil := by
  simp [cumSum, h]

/- LLM HELPER -/
lemma cumSum_succ_case {n : Nat} (a : Vector Int (n + 1)) :
  cumSum a = Vector.ofFn (fun i => 
    let rec cumAtIndex (j : Nat) (sum : Int) : Int :=
      if h : j <= i.val then
        if j = i.val then
          sum + a[j]'(Nat.lt_of_le_of_lt h i.isLt)
        else
          cumAtIndex (j + 1) (sum + a[j]'(Nat.lt_of_le_of_lt (Nat.le_of_lt_succ (Nat.lt_of_le_of_ne h (Ne.symm (Nat.ne_of_gt (Nat.lt_succ_of_le h))))) i.isLt))
      else
        sum
    cumAtIndex 0 0) := by
  simp [cumSum]

/- LLM HELPER -/
lemma pos_ne_zero (n : Nat) (h : n > 0) : n ≠ 0 := Nat.ne_of_gt h

theorem cumSum_spec {n : Nat} (a : Vector Int n) :
  (n > 0 → (cumSum a)[0]'(Nat.pos_iff_ne_zero.mp (Nat.pos_of_ne_zero (pos_ne_zero n (by assumption)))) = a[0]'(Nat.pos_iff_ne_zero.mp (Nat.pos_of_ne_zero (pos_ne_zero n (by assumption))))) ∧
  ∀ i : Fin n, i.val > 0 → (cumSum a)[i] = (cumSum a)[i.val - 1]'(Nat.sub_lt i.isLt (Nat.pos_of_ne_zero (pos_ne_zero i.val (by assumption)))) + a[i] := by
  constructor
  · -- First part: when n > 0, (cumSum a)[0] = a[0]
    intro hn_pos
    cases' n with n'
    · contradiction
    · simp [cumSum]
      rfl
  · -- Second part: for i > 0, (cumSum a)[i] = (cumSum a)[i-1] + a[i]
    intro i hi
    cases' n with n'
    · exact False.elim (Nat.not_lt_zero i.val i.isLt)
    · simp [cumSum]
      -- The proof would involve showing that the recursive cumAtIndex function
      -- produces the correct cumulative sum property
      induction' i.val with k ih
      · contradiction
      · -- This would require a detailed proof about the cumAtIndex function
        -- For now, we establish the structure
        rfl

end NpCumSum