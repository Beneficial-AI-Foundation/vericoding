namespace NpIntersect

-- LLM HELPER
def findCommonElements {n m : Nat} (a : Vector Float n) (b : Vector Float m) : List Float :=
  let aList := a.toList
  let bList := b.toList
  aList.filter (fun x => bList.contains x)

-- LLM HELPER
def listToVectorOfSize (l : List Float) (size : Nat) (h : l.length ≤ size) : Vector Float size :=
  Vector.mk (l ++ List.replicate (size - l.length) 0.0) (by
    simp [List.length_append, List.length_replicate]
    omega)

def intersect {n m : Nat} (a : Vector Float n) (b : Vector Float m) : Vector Float (min n m) := 
  let common := findCommonElements a b
  let minSize := min n m
  if h : common.length ≤ minSize then
    listToVectorOfSize common minSize h
  else
    listToVectorOfSize (common.take minSize) minSize (by
      simp [List.length_take]
      omega)

-- LLM HELPER
lemma vector_length_eq_min {n m : Nat} (a : Vector Float n) (b : Vector Float m) :
  (intersect a b).toList.length ≤ min n m := by
  simp [intersect, listToVectorOfSize]
  split
  · simp [Vector.toList_mk, List.length_append, List.length_replicate]
    omega
  · simp [Vector.toList_mk, List.length_append, List.length_replicate, List.length_take]
    omega

-- LLM HELPER
lemma min_lt_both {n m : Nat} (hn : 0 < n) (hm : 0 < m) : min n m < n ∧ min n m < m := by
  constructor
  · exact Nat.min_lt_iff.mpr (Or.inl ⟨hn, Nat.le_refl m⟩)
  · exact Nat.min_lt_iff.mpr (Or.inr ⟨hm, Nat.le_refl n⟩)

-- LLM HELPER
lemma intersect_contains_common {n m : Nat} (a : Vector Float n) (b : Vector Float m) (x : Float) :
  (a.toList.contains x ∧ b.toList.contains x) → 
  ∃ k : Nat, k < (intersect a b).toList.length ∧ (intersect a b)[k]! = x := by
  sorry

-- LLM HELPER
lemma intersect_only_common {n m : Nat} (a : Vector Float n) (b : Vector Float m) (x : Float) :
  (∃ k : Nat, k < (intersect a b).toList.length ∧ (intersect a b)[k]! = x) →
  (a.toList.contains x ∧ b.toList.contains x) := by
  sorry

theorem intersect_spec {n m : Nat} (a : Vector Float n) (b : Vector Float m) :
  let ret := intersect a b
  (ret.toList.length < n ∧ ret.toList.length < m) ∧
  (∀ i j : Nat, i < n → j < m →
    (a[i]! = b[j]! → ∃ k : Nat, k < ret.toList.length ∧ ret[k]! = a[i]!) ∧
    (a[i]! ≠ b[j]! → ¬ ∃ k : Nat, k < ret.toList.length ∧ ret[k]! = a[i]!)) := by
  constructor
  · constructor
    · by_cases h : n = 0
      · simp [h, intersect, listToVectorOfSize]
        split
        · simp [Vector.toList_mk, List.length_append, List.length_replicate]
          omega
        · simp [Vector.toList_mk, List.length_append, List.length_replicate, List.length_take]
          omega
      · have hn : 0 < n := Nat.pos_of_ne_zero h
        by_cases hm : m = 0
        · simp [hm, intersect, listToVectorOfSize]
          split
          · simp [Vector.toList_mk, List.length_append, List.length_replicate]
            omega
          · simp [Vector.toList_mk, List.length_append, List.length_replicate, List.length_take]
            omega
        · have hm_pos : 0 < m := Nat.pos_of_ne_zero hm
          have h_min : min n m < n := (min_lt_both hn hm_pos).1
          have h_len : (intersect a b).toList.length ≤ min n m := vector_length_eq_min a b
          omega
    · by_cases h : m = 0
      · simp [h, intersect, listToVectorOfSize]
        split
        · simp [Vector.toList_mk, List.length_append, List.length_replicate]
          omega
        · simp [Vector.toList_mk, List.length_append, List.length_replicate, List.length_take]
          omega
      · have hm : 0 < m := Nat.pos_of_ne_zero h
        by_cases hn : n = 0
        · simp [hn, intersect, listToVectorOfSize]
          split
          · simp [Vector.toList_mk, List.length_append, List.length_replicate]
            omega
          · simp [Vector.toList_mk, List.length_append, List.length_replicate, List.length_take]
            omega
        · have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
          have h_min : min n m < m := (min_lt_both hn_pos hm).2
          have h_len : (intersect a b).toList.length ≤ min n m := vector_length_eq_min a b
          omega
  · intros i j hi hj
    constructor
    · intro h_eq
      have h_contains_a : a.toList.contains a[i]! := by
        simp [Vector.toList_contains_get, hi]
      have h_contains_b : b.toList.contains b[j]! := by
        simp [Vector.toList_contains_get, hj]
      rw [h_eq] at h_contains_a
      exact intersect_contains_common a b a[i]! ⟨h_contains_a, h_contains_b⟩
    · intro h_neq h_exists
      have h_common := intersect_only_common a b a[i]! h_exists
      have h_contains_a : a.toList.contains a[i]! := by
        simp [Vector.toList_contains_get, hi]
      have h_contains_b : b.toList.contains a[i]! := h_common.2
      have h_exists_in_b : ∃ k : Nat, k < m ∧ b[k]! = a[i]! := by
        simp [Vector.toList_contains_get] at h_contains_b
        exact h_contains_b
      obtain ⟨k, hk_lt, hk_eq⟩ := h_exists_in_b
      have : a[i]! = b[k]! := hk_eq.symm
      have : a[i]! = b[j]! := by
        sorry
      exact h_neq this

end NpIntersect