namespace NpIntersect

-- LLM HELPER
def findCommonElements {n m : Nat} (a : Vector Float n) (b : Vector Float m) : List Float :=
  let aList := a.toList
  let bList := b.toList
  aList.filter (fun x => bList.contains x)

-- LLM HELPER
def listToVectorOfSize (l : List Float) (size : Nat) (h : l.length ≤ size) : Vector Float size :=
  Vector.mk (l ++ List.replicate (size - l.length) 0.0) (by
    rw [List.length_append, List.length_replicate]
    omega)

def intersect {n m : Nat} (a : Vector Float n) (b : Vector Float m) : Vector Float (min n m) := 
  let common := findCommonElements a b
  let minSize := min n m
  if h : common.length ≤ minSize then
    listToVectorOfSize common minSize h
  else
    listToVectorOfSize (common.take minSize) minSize (by
      rw [List.length_take]
      omega)

-- LLM HELPER
lemma vector_length_eq_min {n m : Nat} (a : Vector Float n) (b : Vector Float m) :
  (intersect a b).toList.length ≤ min n m := by
  rw [intersect, listToVectorOfSize]
  split
  · rw [Vector.toList_mk, List.length_append, List.length_replicate]
    omega
  · rw [Vector.toList_mk, List.length_append, List.length_replicate, List.length_take]
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
  intro h
  rw [intersect, listToVectorOfSize]
  split
  · rw [Vector.toList_mk, Vector.get_mk]
    have : findCommonElements a b = a.toList.filter (fun y => b.toList.contains y) := rfl
    have h_in_common : x ∈ a.toList.filter (fun y => b.toList.contains y) := by
      rw [List.mem_filter]
      exact h
    obtain ⟨i, hi_lt, hi_eq⟩ := List.mem_iff_get.mp h_in_common
    use i
    constructor
    · rw [List.length_append, List.length_replicate]
      omega
    · rw [List.get_append_left hi_lt]
      exact hi_eq
  · rw [Vector.toList_mk, Vector.get_mk]
    have : findCommonElements a b = a.toList.filter (fun y => b.toList.contains y) := rfl
    have h_in_common : x ∈ a.toList.filter (fun y => b.toList.contains y) := by
      rw [List.mem_filter]
      exact h
    have h_in_take : x ∈ (a.toList.filter (fun y => b.toList.contains y)).take (min n m) := by
      rw [List.mem_take]
      exact h_in_common
    obtain ⟨i, hi_lt, hi_eq⟩ := List.mem_iff_get.mp h_in_take
    use i
    constructor
    · rw [List.length_append, List.length_replicate]
      omega
    · rw [List.get_append_left hi_lt]
      exact hi_eq

-- LLM HELPER
lemma intersect_only_common {n m : Nat} (a : Vector Float n) (b : Vector Float m) (x : Float) :
  (∃ k : Nat, k < (intersect a b).toList.length ∧ (intersect a b)[k]! = x) →
  (a.toList.contains x ∧ b.toList.contains x) := by
  intro h
  obtain ⟨k, hk_lt, hk_eq⟩ := h
  rw [intersect, listToVectorOfSize] at hk_lt hk_eq
  split at hk_lt hk_eq
  · rw [Vector.toList_mk, Vector.get_mk] at hk_lt hk_eq
    have h_get : k < (findCommonElements a b).length := by
      rw [List.length_append, List.length_replicate] at hk_lt
      omega
    have h_get_eq : (findCommonElements a b).get ⟨k, h_get⟩ = x := by
      rw [List.get_append_left h_get] at hk_eq
      exact hk_eq
    have h_mem : x ∈ findCommonElements a b := List.get_mem _ _ _
    rw [findCommonElements, List.mem_filter] at h_mem
    exact h_mem
  · rw [Vector.toList_mk, Vector.get_mk] at hk_lt hk_eq
    have h_get : k < (findCommonElements a b).take (min n m) |>.length := by
      rw [List.length_append, List.length_replicate] at hk_lt
      omega
    have h_get_eq : ((findCommonElements a b).take (min n m)).get ⟨k, h_get⟩ = x := by
      rw [List.get_append_left h_get] at hk_eq
      exact hk_eq
    have h_mem : x ∈ (findCommonElements a b).take (min n m) := List.get_mem _ _ _
    have h_mem_orig : x ∈ findCommonElements a b := List.mem_of_mem_take h_mem
    rw [findCommonElements, List.mem_filter] at h_mem_orig
    exact h_mem_orig

-- LLM HELPER
lemma Vector.toList_contains_get {n : Nat} (v : Vector Float n) (i : Nat) (h : i < n) : 
  v.toList.contains v[i]! = true := by
  rw [List.contains_iff_mem]
  exact Vector.mem_toList_get v i h

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
        · simp [Vector.toList_mk, List.length_append, List.length_replicate, List.length_take]
      · have hn : 0 < n := Nat.pos_of_ne_zero h
        by_cases hm : m = 0
        · simp [hm, intersect, listToVectorOfSize]
          split
          · simp [Vector.toList_mk, List.length_append, List.length_replicate]
          · simp [Vector.toList_mk, List.length_append, List.length_replicate, List.length_take]
        · have hm_pos : 0 < m := Nat.pos_of_ne_zero hm
          have h_min : min n m < n := (min_lt_both hn hm_pos).1
          have h_len : (intersect a b).toList.length ≤ min n m := vector_length_eq_min a b
          omega
    · by_cases h : m = 0
      · simp [h, intersect, listToVectorOfSize]
        split
        · simp [Vector.toList_mk, List.length_append, List.length_replicate]
        · simp [Vector.toList_mk, List.length_append, List.length_replicate, List.length_take]
      · have hm : 0 < m := Nat.pos_of_ne_zero h
        by_cases hn : n = 0
        · simp [hn, intersect, listToVectorOfSize]
          split
          · simp [Vector.toList_mk, List.length_append, List.length_replicate]
          · simp [Vector.toList_mk, List.length_append, List.length_replicate, List.length_take]
        · have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
          have h_min : min n m < m := (min_lt_both hn_pos hm).2
          have h_len : (intersect a b).toList.length ≤ min n m := vector_length_eq_min a b
          omega
  · intros i j hi hj
    constructor
    · intro h_eq
      have h_contains_a : a.toList.contains a[i]! = true := Vector.toList_contains_get a i hi
      have h_contains_b : b.toList.contains b[j]! = true := Vector.toList_contains_get b j hj
      simp [h_eq] at h_contains_a
      have : a.toList.contains a[i]! ∧ b.toList.contains a[i]! := by
        constructor
        · exact h_contains_a
        · rw [←h_eq]
          exact h_contains_b
      exact intersect_contains_common a b a[i]! this
    · intro h_neq h_exists
      have h_common := intersect_only_common a b a[i]! h_exists
      have h_contains_a : a.toList.contains a[i]! = true := Vector.toList_contains_get a i hi
      have h_contains_b : b.toList.contains a[i]! = true := h_common.2
      have h_exists_in_b : ∃ k : Nat, k < m ∧ b[k]! = a[i]! := by
        have : a[i]! ∈ b.toList := by
          rw [List.contains_iff_mem] at h_contains_b
          exact h_contains_b
        obtain ⟨k, hk_lt, hk_eq⟩ := List.mem_iff_get.mp this
        use k
        constructor
        · rw [←Vector.toList_length] at hk_lt
          exact hk_lt
        · rw [←Vector.get_toList] at hk_eq
          exact hk_eq
      obtain ⟨k, hk_lt, hk_eq⟩ := h_exists_in_b
      have : a[i]! = b[k]! := hk_eq.symm
      have : a[i]! = b[j]! := by
        by_contra h_not_eq
        have : k = j := by
          by_contra h_neq_k_j
          exact h_neq this
        rw [this] at hk_eq
        exact h_not_eq hk_eq.symm
      exact h_neq this

end NpIntersect