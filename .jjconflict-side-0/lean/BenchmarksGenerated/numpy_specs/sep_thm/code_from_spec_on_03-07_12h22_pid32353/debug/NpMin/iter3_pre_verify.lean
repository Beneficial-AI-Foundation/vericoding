/-
# NumPy Min Specification

Port of np_min.dfy to Lean 4
-/

namespace DafnySpecs.NpMin

/- LLM HELPER -/
def List.minimum_helper : List Int → Option Int
  | [] => none
  | [x] => some x
  | x :: xs => 
    match List.minimum_helper xs with
    | none => some x
    | some y => some (min x y)

/- LLM HELPER -/
lemma List.minimum_helper_none_iff (l : List Int) : 
  List.minimum_helper l = none ↔ l = [] := by
  cases l with
  | nil => simp [List.minimum_helper]
  | cons x xs => 
    simp [List.minimum_helper]
    cases List.minimum_helper xs with
    | none => simp
    | some y => simp

/- LLM HELPER -/
lemma List.minimum_helper_mem (l : List Int) (h : l ≠ []) : 
  ∃ x ∈ l, List.minimum_helper l = some x := by
  induction l with
  | nil => contradiction
  | cons x xs ih =>
    simp [List.minimum_helper]
    cases h_xs : List.minimum_helper xs with
    | none => 
      simp [h_xs]
      exact ⟨x, Or.inl rfl, rfl⟩
    | some y => 
      simp [h_xs]
      have : xs ≠ [] ∨ xs = [] := by simp [Classical.em]
      cases this with
      | inl h_ne => 
        obtain ⟨z, hz_mem, hz_eq⟩ := ih h_ne
        rw [hz_eq] at h_xs
        simp at h_xs
        rw [← h_xs]
        if h_min : x ≤ y then
          simp [min_def, h_min]
          exact ⟨x, Or.inl rfl, rfl⟩
        else
          simp [min_def, h_min]
          exact ⟨y, Or.inr hz_mem, rfl⟩
      | inr h_eq =>
        rw [h_eq] at h_xs
        simp [List.minimum_helper] at h_xs

/- LLM HELPER -/
lemma List.minimum_helper_le (l : List Int) (x : Int) (h_mem : x ∈ l) (h_ne : l ≠ []) :
  ∃ y, List.minimum_helper l = some y ∧ y ≤ x := by
  induction l with
  | nil => contradiction
  | cons a as ih =>
    simp [List.minimum_helper]
    cases h_as : List.minimum_helper as with
    | none =>
      simp [h_as]
      cases h_mem with
      | inl h_eq => 
        rw [← h_eq]
        exact ⟨a, rfl, le_refl a⟩
      | inr h_in => 
        have : as = [] := by
          rw [List.minimum_helper_none_iff] at h_as
          exact h_as
        rw [this] at h_in
        simp at h_in
    | some b =>
      simp [h_as]
      cases h_mem with
      | inl h_eq =>
        rw [← h_eq]
        exact ⟨min a b, rfl, min_le_left a b⟩
      | inr h_in =>
        have h_as_ne : as ≠ [] := by
          intro h_eq
          rw [h_eq] at h_as
          simp [List.minimum_helper] at h_as
        obtain ⟨y, hy_eq, hy_le⟩ := ih h_in h_as_ne
        rw [hy_eq] at h_as
        simp at h_as
        rw [← h_as]
        exact ⟨min a b, rfl, le_trans (min_le_right a b) hy_le⟩

/-- Find the minimum element in a non-empty vector -/
def min {n : Nat} (h : n > 0) (a : Vector Int n) : Int := 
  (List.minimum_helper a.toList).get (by
    simp [List.minimum_helper_none_iff]
    intro h_empty
    have : a.toList.length = n := by simp
    rw [h_empty] at this
    simp at this
    exact Nat.ne_of_gt h this.symm
  )

/-- Specification: The minimum exists in the vector -/
theorem min_exists {n : Nat} (h : n > 0) (a : Vector Int n) :
  ∃ i : Fin n, min h a = a[i] := by
  unfold min
  have h_nonempty : a.toList ≠ [] := by
    intro h_empty
    have : a.toList.length = n := by simp
    rw [h_empty] at this
    simp at this
    exact Nat.ne_of_gt h this.symm
  obtain ⟨x, hx_mem, hx_eq⟩ := List.minimum_helper_mem a.toList h_nonempty
  rw [← hx_eq]
  simp
  rw [List.mem_iff_get] at hx_mem
  obtain ⟨idx, h_eq⟩ := hx_mem
  use ⟨idx, by
    have : a.toList.length = n := by simp
    rw [← this]
    exact idx.isLt
  ⟩
  simp [Vector.get_def]
  exact h_eq.symm

/-- Specification: The minimum is less than or equal to all elements -/
theorem min_spec {n : Nat} (h : n > 0) (a : Vector Int n) :
  ∀ i : Fin n, min h a ≤ a[i] := by
  intro i
  unfold min
  have h_nonempty : a.toList ≠ [] := by
    intro h_empty
    have : a.toList.length = n := by simp
    rw [h_empty] at this
    simp at this
    exact Nat.ne_of_gt h this.symm
  have h_mem : a[i] ∈ a.toList := by
    simp [List.mem_iff_get]
    use ⟨i.val, by
      have : a.toList.length = n := by simp
      rw [this]
      exact i.isLt
    ⟩
    simp [Vector.get_def]
  obtain ⟨y, hy_eq, hy_le⟩ := List.minimum_helper_le a.toList a[i] h_mem h_nonempty
  rw [← hy_eq]
  simp
  exact hy_le

end DafnySpecs.NpMin