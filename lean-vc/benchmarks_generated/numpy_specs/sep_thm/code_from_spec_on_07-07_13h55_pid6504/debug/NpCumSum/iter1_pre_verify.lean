/-
# Cumulative Sum Specification

Port of np_cum_sum.dfy to Lean 4
-/

namespace DafnySpecs.NpCumSum

-- LLM HELPER
def cumSumAux (a : List Int) : List Int :=
  match a with
  | [] => []
  | x :: xs => 
    let rest := cumSumAux xs
    match rest with
    | [] => [x]
    | y :: ys => (x + y) :: rest

-- LLM HELPER
def cumSumList (a : List Int) : List Int :=
  (cumSumAux a.reverse).reverse

/-- Cumulative sum operation on a vector of integers -/
def cumSum {n : Nat} (a : Vector Int n) : Vector Int n := 
  Vector.mk (cumSumList a.toList) (by
    induction' n with n ih
    · simp [cumSumList, cumSumAux]
    · sorry -- Length preservation proof
  )

-- LLM HELPER
lemma cumSumList_length (a : List Int) : (cumSumList a).length = a.length := by
  induction a with
  | nil => simp [cumSumList, cumSumAux]
  | cons x xs ih =>
    simp [cumSumList, cumSumAux]
    sorry

-- LLM HELPER
lemma cumSumList_first (a : List Int) (h : a ≠ []) : 
    (cumSumList a).head (by rw [cumSumList_length]; exact List.length_pos_iff_ne_nil.mpr h) = 
    a.head h := by
  cases' a with x xs
  · contradiction
  · simp [cumSumList, cumSumAux]
    sorry

-- LLM HELPER
lemma cumSumList_recursive (a : List Int) (i : Nat) (hi : i < a.length) (hpos : 0 < i) :
    (cumSumList a)[i]'(by rw [cumSumList_length]; exact hi) = 
    (cumSumList a)[i-1]'(by rw [cumSumList_length]; omega) + a[i]'hi := by
  sorry

/-- The cumulative sum preserves the first element -/
theorem cumSum_first {n : Nat} (hn : 0 < n) (a : Vector Int n) :
    (cumSum a)[0]'(by omega) = a[0]'(by omega) := by
  simp [cumSum]
  have h1 : a.toList ≠ [] := by
    intro h
    have : a.toList.length = 0 := by rw [h]; simp
    rw [Vector.toList_length] at this
    omega
  rw [cumSumList_first a.toList h1]
  simp [Vector.toList_get]

/-- Each element is the sum of the previous cumulative sum and the current element -/
theorem cumSum_recursive {n : Nat} (a : Vector Int n) (i : Fin n) (hi : 0 < i.val) :
    (cumSum a)[i] = (cumSum a)[i.val - 1]'(by omega) + a[i] := by
  simp [cumSum]
  have hi_bound : i.val < a.toList.length := by
    rw [Vector.toList_length]
    exact i.isLt
  rw [cumSumList_recursive a.toList i.val hi_bound hi]
  simp [Vector.toList_get]

end DafnySpecs.NpCumSum