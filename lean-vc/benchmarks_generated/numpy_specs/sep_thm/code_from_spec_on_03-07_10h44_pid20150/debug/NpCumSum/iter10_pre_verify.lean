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
      prev.set ⟨k + 1, h⟩ (prev[k]'(by omega) + a[k + 1]'h)
    else
      cumSumAux a k

/- LLM HELPER -/
lemma cumSumAux_monotone {n : Nat} (a : Vector Int n) (k j : Nat) (hk : k ≤ j) (i : Fin n) (hi : i.val ≤ k) :
    (cumSumAux a k)[i] = (cumSumAux a j)[i] := by
  induction j, hk using Nat.le_induction with
  | base => rfl
  | succ j hkj ih =>
    simp [cumSumAux]
    split_ifs with h
    · simp [Vector.get_set]
      split_ifs with h'
      · omega
      · exact ih
    · exact ih

/- LLM HELPER -/
lemma cumSumAux_ge_preserves {n : Nat} (a : Vector Int n) (k : Nat) (i : Fin n) (hi : k < i.val) :
    (cumSumAux a k)[i] = a[i] := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp [cumSumAux]
    split_ifs with h
    · simp [Vector.get_set]
      split_ifs with h'
      · omega
      · exact ih
    · exact ih

/-- Cumulative sum operation on a vector of integers -/
def cumSum {n : Nat} (a : Vector Int n) : Vector Int n := cumSumAux a (n - 1)

/- LLM HELPER -/
lemma cumSumAux_first {n : Nat} (a : Vector Int n) (k : Nat) (hn : 0 < n) :
    (cumSumAux a k)[0]'(by omega) = a[0]'(by omega) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp [cumSumAux]
    split_ifs with h
    · simp [Vector.get_set]
      split_ifs with h'
      · omega
      · exact ih
    · exact ih

/- LLM HELPER -/
lemma cumSumAux_recursive {n : Nat} (a : Vector Int n) (k : Nat) (i : Fin n) (hi : 0 < i.val) (hk : i.val ≤ k) :
    (cumSumAux a k)[i] = (cumSumAux a k)[i.val - 1]'(by omega) + a[i] := by
  induction k, hk using Nat.le_induction with
  | base =>
    simp [cumSumAux]
    split_ifs with h
    · simp [Vector.get_set]
      split_ifs with h'
      · simp at h'
        rw [cumSumAux_ge_preserves]
        omega
      · omega
    · omega
  | succ k hik ih =>
    simp [cumSumAux]
    split_ifs with h
    · simp [Vector.get_set]
      split_ifs with h'
      · simp at h'
        rw [cumSumAux_monotone a k (k + 1) (by omega)]
        exact ih
      · exact ih
    · exact ih

/-- The cumulative sum preserves the first element -/
theorem cumSum_first {n : Nat} (hn : 0 < n) (a : Vector Int n) :
    (cumSum a)[0]'(by omega) = a[0]'(by omega) := by
  exact cumSumAux_first a (n - 1) hn

/-- Each element is the sum of the previous cumulative sum and the current element -/
theorem cumSum_recursive {n : Nat} (a : Vector Int n) (i : Fin n) (hi : 0 < i.val) :
    (cumSum a)[i] = (cumSum a)[i.val - 1]'(by omega) + a[i] := by
  exact cumSumAux_recursive a (n - 1) i hi (by omega)

end DafnySpecs.NpCumSum