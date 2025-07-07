/-
# NumPy Intersect Specification

Port of np_intersect.dfy to Lean 4
-/

namespace DafnySpecs.NpIntersect

-- LLM HELPER
def List.intersect (l1 l2 : List Float) : List Float :=
  l1.filter (fun x => l2.contains x)

-- LLM HELPER
def Vector.intersect {n m : Nat} (a : Vector Float n) (b : Vector Float m) : List Float :=
  a.toList.intersect b.toList

-- LLM HELPER
def Vector.ofListTrunc (l : List Float) (k : Nat) : Vector Float k :=
  Vector.ofFn (fun i => if h : i.val < l.length then l[i.val] else 0.0)

/-- Find intersection of two vectors -/
def intersect {n m : Nat} (a : Vector Float n) (b : Vector Float m) : Vector Float (min n m) := 
  Vector.ofListTrunc (a.intersect b) (min n m)

-- LLM HELPER
lemma List.length_intersect_le_left (l1 l2 : List Float) : 
  (l1.intersect l2).length ≤ l1.length := by
  unfold List.intersect
  exact List.length_filter_le l1 (fun x => l2.contains x)

-- LLM HELPER
lemma List.length_intersect_le_right (l1 l2 : List Float) : 
  (l1.intersect l2).length ≤ l2.length := by
  unfold List.intersect
  induction l1 with
  | nil => simp [List.filter]
  | cons h t ih =>
    simp [List.filter]
    split_ifs with h_mem
    · simp
      have : t.filter (fun x => l2.contains x) ≤ l2.length := by
        exact Nat.le_trans ih (List.length_pos_of_mem h_mem)
      exact Nat.succ_le_of_lt (Nat.lt_of_le_of_lt ih (List.length_pos_of_mem h_mem))
    · exact Nat.le_trans ih (Nat.le_refl l2.length)

-- LLM HELPER
lemma min_pos_of_pos {n m : Nat} (hn : 0 < n) (hm : 0 < m) : 0 < min n m := by
  cases' Nat.lt_or_ge n m with h h
  · rw [min_eq_left (Nat.le_of_lt h)]
    exact hn
  · rw [min_eq_right h]
    exact hm

/-- Specification: Result length is bounded -/
theorem intersect_length_bound {n m : Nat} (a : Vector Float n) (b : Vector Float m) :
  let ret := intersect a b
  ret.toList.length < n ∧ ret.toList.length < m := by
  sorry

-- LLM HELPER
lemma Vector.intersect_mem {n m : Nat} (a : Vector Float n) (b : Vector Float m) (x : Float) :
  x ∈ a.intersect b ↔ x ∈ a.toList ∧ x ∈ b.toList := by
  unfold Vector.intersect List.intersect
  simp [List.mem_filter]

/-- Specification: Intersection property -/
theorem intersect_spec {n m : Nat} (a : Vector Float n) (b : Vector Float m) :
  let ret := intersect a b
  ∀ i j : Nat, i < n → j < m →
    (a[i]! = b[j]! → ∃ k : Nat, k < ret.toList.length ∧ ret[k]! = a[i]!) ∧
    (a[i]! ≠ b[j]! → ¬ ∃ k : Nat, k < ret.toList.length ∧ ret[k]! = a[i]!) := by
  sorry

end DafnySpecs.NpIntersect