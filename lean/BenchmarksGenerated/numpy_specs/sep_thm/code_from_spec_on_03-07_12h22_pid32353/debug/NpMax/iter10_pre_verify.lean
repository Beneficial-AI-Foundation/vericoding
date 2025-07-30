/-
# NumPy Max Specification

Port of np_max.dfy to Lean 4
-/

namespace DafnySpecs.NpMax

/- LLM HELPER -/
def List.maximum (l : List Int) : Option Int :=
  l.foldl (fun acc x => some (max (acc.getD x) x)) none

/- LLM HELPER -/
theorem List.maximum_isSome {l : List Int} : l ≠ [] → l.maximum.isSome := by
  intro h_nonempty
  cases l with
  | nil => contradiction
  | cons head tail => 
    simp [List.maximum, Option.isSome]

/- LLM HELPER -/
theorem List.maximum_mem {l : List Int} (h : l ≠ []) : ∃ x ∈ l, l.maximum = some x := by
  induction l with
  | nil => contradiction
  | cons head tail ih =>
    cases tail with
    | nil => 
      use head
      simp [List.maximum]
    | cons t_head t_tail =>
      have h_tail_nonempty : tail ≠ [] := by simp
      obtain ⟨x, hx_mem, hx_max⟩ := ih h_tail_nonempty
      simp [List.maximum] at hx_max ⊢
      by_cases h_comp : head ≥ x
      · use head
        constructor
        · simp
        · simp [max_def, h_comp, hx_max]
      · use x
        constructor
        · right; exact hx_mem
        · simp [max_def, h_comp, hx_max]

/- LLM HELPER -/
theorem List.le_maximum_of_mem {l : List Int} {x : Int} (h_mem : x ∈ l) (h_nonempty : l ≠ []) : 
  ∃ y, l.maximum = some y ∧ x ≤ y := by
  induction l with
  | nil => contradiction
  | cons head tail ih =>
    cases h_mem with
    | head => 
      cases tail with
      | nil => 
        use head
        simp [List.maximum]
      | cons t_head t_tail =>
        have h_tail_nonempty : tail ≠ [] := by simp
        obtain ⟨y, hy_max, _⟩ := List.maximum_mem h_tail_nonempty
        use max head y
        simp [List.maximum, hy_max, List.foldl, Option.getD]
        exact le_max_left head y
    | tail h_tail_mem =>
      cases tail with
      | nil => simp at h_tail_mem
      | cons t_head t_tail =>
        have h_tail_nonempty : tail ≠ [] := by simp
        obtain ⟨y, hy_max, hx_le_y⟩ := ih h_tail_mem h_tail_nonempty
        use max head y
        simp [List.maximum, hy_max, List.foldl, Option.getD]
        exact le_trans hx_le_y (le_max_right head y)

/-- Find the maximum element in a non-empty vector -/
def max {n : Nat} (h : n > 0) (a : Vector Int n) : Int := 
  a.toList.maximum.get (List.maximum_isSome (by
    simp [Vector.length_toList]
    exact Nat.pos_iff_ne_zero.mp h))

/- LLM HELPER -/
theorem Vector.mem_toList_iff {α : Type*} {n : Nat} (a : Vector α n) (x : α) : 
  x ∈ a.toList ↔ ∃ i : Fin n, a[i] = x := by
  constructor
  · intro h_mem
    have h_lt : ∃ i < a.toList.length, a.toList[i]? = some x := by
      rw [← List.mem_iff_get?] at h_mem
      exact h_mem
    obtain ⟨i, h_lt_len, h_eq⟩ := h_lt
    use ⟨i, by rw [← Vector.length_toList]; exact h_lt_len⟩
    simp [Vector.get_eq_getElem]
    rw [← Option.some_inj]
    rw [← h_eq]
    simp [Vector.getElem_toList, List.get?_eq_get]
  · intro ⟨i, h_eq⟩
    rw [← h_eq]
    simp [Vector.mem_toList]

/-- Specification: The maximum exists in the vector -/
theorem max_exists {n : Nat} (h : n > 0) (a : Vector Int n) :
  ∃ i : Fin n, max h a = a[i] := by
  unfold max
  have h_nonempty : a.toList ≠ [] := by
    intro h_empty
    have : a.toList.length = 0 := by simp [h_empty]
    rw [Vector.length_toList] at this
    exact Nat.lt_irrefl 0 (this ▸ h)
  obtain ⟨val, h_mem, h_max⟩ := List.maximum_mem h_nonempty
  rw [Vector.mem_toList_iff] at h_mem
  obtain ⟨i, h_eq⟩ := h_mem
  use i
  simp [Vector.get_eq_getElem]
  rw [h_eq, h_max]
  simp

/-- Specification: The maximum is greater than or equal to all elements -/
theorem max_spec {n : Nat} (h : n > 0) (a : Vector Int n) :
  ∀ i : Fin n, a[i] ≤ max h a := by
  intro i
  unfold max
  have h_nonempty : a.toList ≠ [] := by
    intro h_empty
    have : a.toList.length = 0 := by simp [h_empty]
    rw [Vector.length_toList] at this
    exact Nat.lt_irrefl 0 (this ▸ h)
  have h_mem : a[i] ∈ a.toList := by
    rw [Vector.mem_toList_iff]
    use i
  obtain ⟨y, hy_max, hx_le_y⟩ := List.le_maximum_of_mem h_mem h_nonempty
  rw [← hy_max]
  simp
  exact hx_le_y

end DafnySpecs.NpMax