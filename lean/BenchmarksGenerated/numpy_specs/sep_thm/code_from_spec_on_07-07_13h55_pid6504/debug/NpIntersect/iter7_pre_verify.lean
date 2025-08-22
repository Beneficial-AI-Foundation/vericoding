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
lemma Vector.toList_length_eq {n : Nat} (v : Vector Float n) : v.toList.length = n := by
  exact Vector.toList_length v

-- LLM HELPER
lemma Vector.getElem_mem_toList {n : Nat} (v : Vector Float n) (i : Nat) (hi : i < n) : v[i]! ∈ v.toList := by
  rw [Vector.getElem_eq_get]
  exact Vector.get_mem v ⟨i, hi⟩

-- LLM HELPER
lemma Vector.toList_ofListTrunc_length (l : List Float) (k : Nat) : 
  (Vector.ofListTrunc l k).toList.length = k := by
  unfold Vector.ofListTrunc
  exact Vector.toList_length _

/-- Specification: Result length is bounded -/
theorem intersect_length_bound {n m : Nat} (a : Vector Float n) (b : Vector Float m) :
  let ret := intersect a b
  ret.toList.length ≤ n ∧ ret.toList.length ≤ m := by
  unfold intersect
  simp [Vector.toList_ofListTrunc_length]
  constructor
  · exact Nat.min_le_left n m
  · exact Nat.min_le_right n m

-- LLM HELPER
lemma Vector.intersect_mem {n m : Nat} (a : Vector Float n) (b : Vector Float m) (x : Float) :
  x ∈ a.intersect b ↔ x ∈ a.toList ∧ x ∈ b.toList := by
  unfold Vector.intersect List.intersect
  simp [List.mem_filter]

-- LLM HELPER
lemma Vector.getElem_ofListTrunc (l : List Float) (k : Nat) (i : Nat) (hi : i < k) :
  (Vector.ofListTrunc l k)[i]! = if h : i < l.length then l[i]! else 0.0 := by
  unfold Vector.ofListTrunc
  rw [Vector.getElem_ofFn]
  congr

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
      constructor
      · exact h_mem_a
      · rw [← h_eq]
        exact Vector.getElem_mem_toList b j hj
    cases' List.mem_iff_get.mp h_in_intersect with k hk
    use k
    constructor
    · simp [Vector.toList_ofListTrunc_length]
      exact hk.1
    · simp [Vector.getElem_ofListTrunc]
      exact hk.2
  · intro h_neq
    intro ⟨k, hk_lt, hk_eq⟩
    unfold intersect at hk_eq hk_lt
    simp [Vector.getElem_ofListTrunc] at hk_eq
    have h_mem_intersect : a[i]! ∈ a.intersect b := by
      rw [← hk_eq]
      have h_mem_a : a[i]! ∈ a.toList := Vector.getElem_mem_toList a i hi
      rw [Vector.intersect_mem]
      constructor
      · exact h_mem_a
      · rw [← hk_eq]
        have : ret[k]! ∈ ret.toList := by
          have : k < ret.toList.length := hk_lt
          exact List.getElem_mem ret.toList k
        have : ret[k]! ∈ a.intersect b := by
          unfold intersect at this
          simp [Vector.toList_ofListTrunc_length] at this
          exact this
        rw [Vector.intersect_mem] at this
        exact this.2
    rw [Vector.intersect_mem] at h_mem_intersect
    have ⟨_, h_mem_b⟩ := h_mem_intersect
    have h_eq : a[i]! = b[j]! := by
      have h_mem_b_j : b[j]! ∈ b.toList := Vector.getElem_mem_toList b j hj
      have h_a_eq : a[i]! = ret[k]! := by
        exact hk_eq.symm
      rw [h_a_eq]
      rw [← hk_eq]
      exact Classical.choose_spec (Classical.choose_spec h_mem_b)
    exact h_neq h_eq

end DafnySpecs.NpIntersect