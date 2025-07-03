/-
# Cumulative Sum Specification

Port of np_cum_sum.dfy to Lean 4
-/

namespace DafnySpecs.NpCumSum

/- LLM HELPER -/
def cumSumAux {n : Nat} (a : Vector Int n) : Nat → Vector Int n
  | 0 => a
  | k + 1 => 
    if h : k + 1 < n then
      let prev := cumSumAux a k
      have h_k : k < n := by omega
      prev.set ⟨k + 1, h⟩ (prev[k]'h_k + a[k + 1]'h)
    else
      cumSumAux a k

/- LLM HELPER -/
def cumSumHelper {n : Nat} (a : Vector Int n) (i : Nat) : Vector Int n :=
  if i = 0 then a
  else 
    let prev := cumSumHelper a (i - 1)
    if h : i < n then
      have h_prev : i - 1 < n := by omega
      prev.set ⟨i, h⟩ (prev[i - 1]'h_prev + a[i]'h)
    else prev

/-- Cumulative sum operation on a vector of integers -/
def cumSum {n : Nat} (a : Vector Int n) : Vector Int n := 
  if n = 0 then a
  else
    let rec go (i : Nat) (acc : Vector Int n) : Vector Int n :=
      if i >= n then acc
      else
        let prev_idx := i - 1
        if h : i < n then
          if i = 0 then
            go (i + 1) acc
          else
            have h_prev : prev_idx < n := by omega
            let new_val := acc[prev_idx]'h_prev + a[i]'h
            go (i + 1) (acc.set ⟨i, h⟩ new_val)
        else acc
    go 1 a

/- LLM HELPER -/
lemma cumSum_zero_eq {n : Nat} (a : Vector Int n) (hn : 0 < n) :
    (cumSum a)[0]'(by omega) = a[0]'(by omega) := by
  simp [cumSum]
  split
  · omega
  · simp [Vector.get]

/-- The cumulative sum preserves the first element -/
theorem cumSum_first {n : Nat} (hn : 0 < n) (a : Vector Int n) :
    (cumSum a)[0]'(by omega) = a[0]'(by omega) := by
  exact cumSum_zero_eq a hn

/- LLM HELPER -/
lemma cumSum_step {n : Nat} (a : Vector Int n) (i : Fin n) (hi : 0 < i.val) :
    (cumSum a)[i] = (cumSum a)[i.val - 1]'(by omega) + a[i] := by
  simp [cumSum]
  split
  · omega
  · induction i.val using Nat.strong_induction_on with
    | ind k ih => 
      simp
      split
      · omega
      · simp [Vector.get]
        split
        · omega
        · rfl

/-- Each element is the sum of the previous cumulative sum and the current element -/
theorem cumSum_recursive {n : Nat} (a : Vector Int n) (i : Fin n) (hi : 0 < i.val) :
    (cumSum a)[i] = (cumSum a)[i.val - 1]'(by omega) + a[i] := by
  exact cumSum_step a i hi

end DafnySpecs.NpCumSum