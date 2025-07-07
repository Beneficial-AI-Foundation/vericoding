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
    | y :: _ => (x + y) :: rest

-- LLM HELPER
def cumSumList (a : List Int) : List Int :=
  (cumSumAux a.reverse).reverse

-- LLM HELPER
lemma cumSumAux_length (a : List Int) : (cumSumAux a).length = a.length := by
  induction a with
  | nil => simp [cumSumAux]
  | cons x xs ih =>
    simp [cumSumAux]
    cases' cumSumAux xs with y ys
    · simp
      rw [ih]
      simp
    · simp
      rw [ih]

-- LLM HELPER
lemma cumSumList_length (a : List Int) : (cumSumList a).length = a.length := by
  simp [cumSumList]
  rw [List.length_reverse, cumSumAux_length, List.length_reverse]

-- LLM HELPER
lemma cumSumList_first (a : List Int) (h : a ≠ []) : 
    (cumSumList a).head (by rw [cumSumList_length]; exact List.length_pos_iff_ne_nil.mpr h) = 
    a.head h := by
  cases' a with x xs
  · contradiction
  · simp [cumSumList, cumSumAux]
    cases' xs with y ys
    · simp
    · simp [cumSumAux]
      cases' cumSumAux (y :: ys).reverse with z zs
      · simp [cumSumAux_length] at *
      · simp

-- LLM HELPER
lemma cumSumList_recursive (a : List Int) (i : Nat) (hi : i < a.length) (hpos : 0 < i) :
    (cumSumList a)[i]'(by rw [cumSumList_length]; exact hi) = 
    (cumSumList a)[i-1]'(by rw [cumSumList_length]; omega) + a[i]'hi := by
  simp [cumSumList]
  induction' a generalizing i with x xs ih
  · simp at hi
  · cases' i with i'
    · omega
    · simp at hpos hi
      simp [cumSumAux]
      cases' cumSumAux (x :: xs).reverse with z zs
      · simp [cumSumAux_length] at *
      · simp
        rw [List.reverse_cons, cumSumAux_length] at *
        simp

/-- Cumulative sum operation on a vector of integers -/
def cumSum {n : Nat} (a : Vector Int n) : Vector Int n := 
  Vector.mk (cumSumList a.toList).toArray (by
    rw [List.size_toArray, cumSumList_length, a.toList.length]
    exact a.2
  )

/-- The cumulative sum preserves the first element -/
theorem cumSum_first {n : Nat} (hn : 0 < n) (a : Vector Int n) :
    (cumSum a)[0]'(by omega) = a[0]'(by omega) := by
  simp [cumSum]
  have h1 : a.toList ≠ [] := by
    intro h
    have : a.toList.length = 0 := by rw [h]; simp
    rw [a.toList.length] at this
    have : a.val.length = 0 := by simpa using this
    rw [← a.property] at this
    omega
  rw [cumSumList_first a.toList h1]
  rfl

/-- Each element is the sum of the previous cumulative sum and the current element -/
theorem cumSum_recursive {n : Nat} (a : Vector Int n) (i : Fin n) (hi : 0 < i.val) :
    (cumSum a)[i] = (cumSum a)[i.val - 1]'(by omega) + a[i] := by
  simp [cumSum]
  have hi_bound : i.val < a.toList.length := by
    rw [a.toList.length]
    exact i.isLt
  rw [cumSumList_recursive a.toList i.val hi_bound hi]
  rfl

end DafnySpecs.NpCumSum