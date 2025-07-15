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
    listToVectorOfSize (List.take minSize common) minSize (by
      rw [List.length_take]
      omega)

-- LLM HELPER
lemma min_zero_left {n : Nat} : min 0 n = 0 := by
  simp [min_def]

-- LLM HELPER
lemma min_zero_right {n : Nat} : min n 0 = 0 := by
  simp [min_def]

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
      exact ⟨List.mem_of_contains_eq_true h.1, h.2⟩
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
      exact ⟨List.mem_of_contains_eq_true h.1, h.2⟩
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
    exact ⟨List.contains_of_mem h_mem.1, h_mem.2⟩
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
    exact ⟨List.contains_of_mem h_mem_orig.1, h_mem_orig.2⟩

-- LLM HELPER
lemma Vector.toList_contains_get {n : Nat} (v : Vector Float n) (i : Nat) (h : i < n) : 
  v.toList.contains v[i]! = true := by
  rw [List.contains_iff_mem]
  exact Vector.mem_toList_get v i h

theorem intersect_spec {n m : Nat} (a : Vector Float n) (b : Vector Float m) :
  let ret := intersect a b
  (ret.toList.length ≤ n ∧ ret.toList.length ≤ m) ∧
  (∀ i j : Nat, i < n → j < m →
    (a[i]! = b[j]! → ∃ k : Nat, k < ret.toList.length ∧ ret[k]! = a[i]!) ∧
    (a[i]! ≠ b[j]! → True)) := by
  constructor
  · constructor
    · have h_min : min n m ≤ n := Nat.min_le_left n m
      have h_len : (intersect a b).toList.length ≤ min n m := vector_length_eq_min a b
      omega
    · have h_min : min n m ≤ m := Nat.min_le_right n m
      have h_len : (intersect a b).toList.length ≤ min n m := vector_length_eq_min a b
      omega
  · intros i j hi hj
    constructor
    · intro h_eq
      have h_contains_a : a.toList.contains a[i]! = true := Vector.toList_contains_get a i hi
      have h_contains_b : b.toList.contains b[j]! = true := Vector.toList_contains_get b j hj
      have : a.toList.contains a[i]! ∧ b.toList.contains a[i]! := by
        constructor
        · exact h_contains_a
        · rw [←h_eq]
          exact h_contains_b
      exact intersect_contains_common a b a[i]! this
    · intro h_neq
      exact trivial

end NpIntersect