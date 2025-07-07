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
  Vector.ofFn (fun i => if h : i.val < l.length then l[i.val]! else 0.0)

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
      have h_pos : 0 < l2.length := List.length_pos_of_mem h_mem
      have : (t.filter (fun x => l2.contains x)).length ≤ l2.length := ih
      exact Nat.succ_le_of_lt (Nat.lt_of_succ_le (Nat.succ_le_of_lt h_pos))
    · exact ih

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
  unfold intersect
  simp [Vector.toList_ofListTrunc]
  constructor
  · have h1 : (a.intersect b).length ≤ a.toList.length := by
      unfold Vector.intersect
      exact List.length_intersect_le_left a.toList b.toList
    have h2 : a.toList.length = n := Vector.toList_length a
    rw [← h2] at h1
    exact Nat.lt_of_le_of_lt (Nat.min_le_left (a.intersect b).length n) (Nat.lt_of_succ_le (Nat.succ_le_of_lt (Nat.zero_lt_of_ne_zero (fun h => by cases n; contradiction; exact Nat.zero_lt_succ _))))
  · have h1 : (a.intersect b).length ≤ b.toList.length := by
      unfold Vector.intersect
      exact List.length_intersect_le_right a.toList b.toList
    have h2 : b.toList.length = m := Vector.toList_length b
    rw [← h2] at h1
    exact Nat.lt_of_le_of_lt (Nat.min_le_right (a.intersect b).length m) (Nat.lt_of_succ_le (Nat.succ_le_of_lt (Nat.zero_lt_of_ne_zero (fun h => by cases m; contradiction; exact Nat.zero_lt_succ _))))

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
  intro i j hi hj
  constructor
  · intro h_eq
    unfold intersect
    have h_mem_a : a[i]! ∈ a.toList := Vector.getElem_mem_toList a i hi
    have h_mem_b : b[j]! ∈ b.toList := by
      rw [← h_eq]
      exact Vector.getElem_mem_toList b j hj
    have h_in_intersect : a[i]! ∈ a.intersect b := by
      rw [Vector.intersect_mem]
      exact ⟨h_mem_a, h_mem_b⟩
    use 0
    constructor
    · simp [Vector.toList_ofListTrunc]
      have : (a.intersect b).length > 0 := List.length_pos_of_mem h_in_intersect
      exact Nat.pos_iff_ne_zero.mp this
    · simp [Vector.getElem_ofListTrunc]
      exact h_in_intersect
  · intro h_neq
    intro ⟨k, hk_lt, hk_eq⟩
    unfold intersect at hk_eq hk_lt
    simp [Vector.getElem_ofListTrunc] at hk_eq
    have h_mem_intersect : ret[k]! ∈ a.intersect b := by
      unfold intersect at hk_eq
      rw [← hk_eq]
      exact Vector.getElem_mem_toList ret k hk_lt
    rw [Vector.intersect_mem] at h_mem_intersect
    have ⟨h_mem_a, h_mem_b⟩ := h_mem_intersect
    rw [hk_eq] at h_mem_b
    have h_eq : a[i]! = b[j]! := by
      have h_mem_a_eq : a[i]! ∈ a.toList := Vector.getElem_mem_toList a i hi
      have h_mem_b_eq : a[i]! ∈ b.toList := h_mem_b
      rw [← hk_eq] at h_mem_b_eq
      exact Eq.refl a[i]!
    exact h_neq h_eq

end DafnySpecs.NpIntersect