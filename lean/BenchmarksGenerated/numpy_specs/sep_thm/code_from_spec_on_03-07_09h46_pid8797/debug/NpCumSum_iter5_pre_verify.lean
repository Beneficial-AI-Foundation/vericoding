/-
# Cumulative Sum Specification

Port of np_cum_sum.dfy to Lean 4
-/

namespace DafnySpecs.NpCumSum

/- LLM HELPER -/
def cumSumAux {n : Nat} (a : Vector Int n) : Nat → Int
  | 0 => if h : 0 < n then a[0]'(by omega) else 0
  | k + 1 => if h : k + 1 < n then cumSumAux a k + a[k + 1]'h else 0

/- LLM HELPER -/
lemma cumSumAux_valid {n : Nat} (a : Vector Int n) (i : Nat) (hi : i < n) :
    cumSumAux a i = if i = 0 then a[0]'(by omega) else cumSumAux a (i - 1) + a[i]'hi := by
  cases i with
  | zero => 
    simp [cumSumAux]
    rw [if_pos]
    omega
  | succ k =>
    simp [cumSumAux]
    rw [if_pos hi]
    simp [Nat.succ_sub_succ_eq_sub, Nat.sub_zero]

/-- Cumulative sum operation on a vector of integers -/
def cumSum {n : Nat} (a : Vector Int n) : Vector Int n := 
  Vector.ofFn (fun i => cumSumAux a i.val)

/-- The cumulative sum preserves the first element -/
theorem cumSum_first {n : Nat} (hn : 0 < n) (a : Vector Int n) :
    (cumSum a)[0]'(by omega) = a[0]'(by omega) := by
  simp [cumSum]
  simp [cumSumAux]
  rw [dif_pos hn]

/-- Each element is the sum of the previous cumulative sum and the current element -/
theorem cumSum_recursive {n : Nat} (a : Vector Int n) (i : Fin n) (hi : 0 < i.val) :
    (cumSum a)[i] = (cumSum a)[i.val - 1]'(by omega) + a[i] := by
  simp [cumSum]
  rw [cumSumAux_valid a i.val i.isLt]
  simp [hi]
  congr 1
  simp [cumSum]

end DafnySpecs.NpCumSum