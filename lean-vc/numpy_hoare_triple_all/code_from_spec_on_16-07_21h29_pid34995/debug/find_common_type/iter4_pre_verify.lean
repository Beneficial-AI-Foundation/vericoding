import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- Data type representation for NumPy types -/
inductive DType where
  /-- 8-bit signed integer -/
  | int8 
  /-- 16-bit signed integer -/
  | int16 
  /-- 32-bit signed integer -/
  | int32 
  /-- 64-bit signed integer -/
  | int64
  /-- 8-bit unsigned integer -/
  | uint8 
  /-- 16-bit unsigned integer -/
  | uint16 
  /-- 32-bit unsigned integer -/
  | uint32 
  /-- 64-bit unsigned integer -/
  | uint64
  /-- 32-bit floating point -/
  | float32 
  /-- 64-bit floating point -/
  | float64
  /-- 64-bit complex number -/
  | complex64 
  /-- 128-bit complex number -/
  | complex128
  /-- Boolean type -/
  | bool
  /-- Object type -/
  | object

/-- Type hierarchy for promotion rules -/
def DType.kind : DType → Char
  | DType.bool => 'b'
  | DType.int8 | DType.int16 | DType.int32 | DType.int64 => 'i'
  | DType.uint8 | DType.uint16 | DType.uint32 | DType.uint64 => 'u'
  | DType.float32 | DType.float64 => 'f'
  | DType.complex64 | DType.complex128 => 'c'
  | DType.object => 'O'

/-- Type precedence for promotion (higher values have higher precedence) -/
def DType.precedence : DType → Nat
  | DType.bool => 0
  | DType.int8 => 1
  | DType.int16 => 2
  | DType.int32 => 3
  | DType.int64 => 4
  | DType.uint8 => 5
  | DType.uint16 => 6
  | DType.uint32 => 7
  | DType.uint64 => 8
  | DType.float32 => 9
  | DType.float64 => 10
  | DType.complex64 => 11
  | DType.complex128 => 12
  | DType.object => 13

-- LLM HELPER
def List.maxBy (l : List α) (f : α → Nat) : Option α :=
  match l with
  | [] => none
  | [x] => some x
  | x :: xs => 
    match List.maxBy xs f with
    | none => some x
    | some y => if f x ≥ f y then some x else some y

-- LLM HELPER
def Vector.maxBy {n : Nat} (v : Vector α n) (f : α → Nat) : Option α :=
  List.maxBy v.toList f

/-- numpy.find_common_type: Determine common type following standard coercion rules.
    
    This function determines the common data type by following NumPy's type promotion rules.
    It returns the maximum of array_types ignoring scalar_types, unless the maximum of 
    scalar_types is of a different kind (dtype.kind).
    
    Note: This function is deprecated in NumPy 1.25.0 in favor of numpy.result_type.
-/
def find_common_type {n m : Nat} (array_types : Vector DType n) (scalar_types : Vector DType m) : Id (Option DType) := do
  let max_array := array_types.maxBy DType.precedence
  let max_scalar := scalar_types.maxBy DType.precedence
  
  match max_array, max_scalar with
  | none, none => pure none
  | some dt, none => pure (some dt)
  | none, some dt => pure (some dt)
  | some arr_dt, some scl_dt =>
    if arr_dt.kind = scl_dt.kind then
      pure (some arr_dt)
    else
      pure (some scl_dt)

-- LLM HELPER
lemma List.maxBy_mem {α : Type*} (l : List α) (f : α → Nat) (h : l ≠ []) :
  ∃ x, List.maxBy l f = some x ∧ x ∈ l := by
  induction l with
  | nil => contradiction
  | cons head tail ih =>
    simp [List.maxBy]
    cases tail with
    | nil => 
      simp [List.maxBy]
      exact ⟨head, rfl, List.mem_singleton.mpr rfl⟩
    | cons _ _ =>
      have h_ne : tail ≠ [] := by simp
      obtain ⟨y, hy_eq, hy_mem⟩ := ih h_ne
      simp [List.maxBy] at hy_eq
      rw [hy_eq]
      by_cases h_cmp : f head ≥ f y
      · simp [h_cmp]
        exact ⟨head, rfl, List.mem_cons_self _ _⟩
      · simp [h_cmp]
        exact ⟨y, rfl, List.mem_cons_of_mem _ hy_mem⟩

-- LLM HELPER
lemma List.maxBy_max {α : Type*} (l : List α) (f : α → Nat) (x : α) (h_mem : x ∈ l) :
  ∃ y, List.maxBy l f = some y ∧ f x ≤ f y := by
  induction l with
  | nil => cases h_mem
  | cons head tail ih =>
    simp [List.maxBy]
    cases tail with
    | nil =>
      simp [List.maxBy]
      simp at h_mem
      rw [h_mem]
      exact ⟨head, rfl, le_refl _⟩
    | cons _ _ =>
      cases h_mem with
      | head => 
        have h_ne : tail ≠ [] := by simp
        obtain ⟨z, hz_eq, _⟩ := List.maxBy_mem tail f h_ne
        simp [List.maxBy] at hz_eq
        rw [hz_eq]
        by_cases h_cmp : f head ≥ f z
        · simp [h_cmp]
          exact ⟨head, rfl, le_refl _⟩
        · simp [h_cmp]
          exact ⟨z, rfl, le_of_not_ge h_cmp⟩
      | tail h_tail =>
        obtain ⟨y, hy_eq, hy_le⟩ := ih h_tail
        simp [List.maxBy] at hy_eq
        rw [hy_eq]
        by_cases h_cmp : f head ≥ f y
        · simp [h_cmp]
          exact ⟨head, rfl, le_trans hy_le (le_of_not_ge h_cmp)⟩
        · simp [h_cmp]
          exact ⟨y, rfl, hy_le⟩

/-- Specification: find_common_type implements NumPy's type promotion rules correctly.
    
    The function should:
    1. Return the maximum precedence type from array_types if scalar_types is empty
    2. Return the maximum precedence type from scalar_types if array_types is empty  
    3. If both are non-empty, return the maximum from array_types unless the maximum
       from scalar_types has a different kind, in which case return the scalar maximum
    4. Handle the case where type promotion results in a valid common type
    
    Precondition: At least one of the input vectors is non-empty
    Postcondition: The result follows NumPy's documented type promotion rules
-/
theorem find_common_type_spec {n m : Nat} (array_types : Vector DType n) (scalar_types : Vector DType m) 
    (h_nonempty : n > 0 ∨ m > 0) :
    ⦃⌜n > 0 ∨ m > 0⌝⦄
    find_common_type array_types scalar_types
    ⦃⇓result => ⌜
      -- Case 1: Only array types provided
      (m = 0 ∧ n > 0 → ∃ (dt : DType), result = some dt ∧ 
        dt ∈ array_types.toList ∧ 
        ∀ (other : DType), other ∈ array_types.toList → other.precedence ≤ dt.precedence) ∧
      -- Case 2: Only scalar types provided  
      (n = 0 ∧ m > 0 → ∃ (dt : DType), result = some dt ∧ 
        dt ∈ scalar_types.toList ∧ 
        ∀ (other : DType), other ∈ scalar_types.toList → other.precedence ≤ dt.precedence) ∧
      -- Case 3: Both array and scalar types provided
      (n > 0 ∧ m > 0 → 
        ∃ (max_array max_scalar : DType),
          max_array ∈ array_types.toList ∧ max_scalar ∈ scalar_types.toList ∧
          (∀ dt ∈ array_types.toList, dt.precedence ≤ max_array.precedence) ∧
          (∀ dt ∈ scalar_types.toList, dt.precedence ≤ max_scalar.precedence) ∧
          ((max_array.kind = max_scalar.kind → result = some max_array) ∧
           (max_array.kind ≠ max_scalar.kind → result = some max_scalar)))
    ⌝⦄ := by
  simp [find_common_type]
  constructor
  · intro h_case1
    obtain ⟨h_m_zero, h_n_pos⟩ := h_case1
    have h_ne : array_types.toList ≠ [] := by
      simp [Vector.toList_length]
      exact Nat.pos_iff_ne_zero.mp h_n_pos
    obtain ⟨dt, h_eq, h_mem⟩ := List.maxBy_mem array_types.toList DType.precedence h_ne
    simp [Vector.maxBy] at h_eq
    rw [h_eq]
    rw [h_m_zero]
    simp [Vector.maxBy]
    exact ⟨dt, rfl, h_mem, fun other h_other => 
      (List.maxBy_max array_types.toList DType.precedence other h_other).choose_spec.2⟩
  constructor
  · intro h_case2
    obtain ⟨h_n_zero, h_m_pos⟩ := h_case2
    have h_ne : scalar_types.toList ≠ [] := by
      simp [Vector.toList_length]
      exact Nat.pos_iff_ne_zero.mp h_m_pos
    obtain ⟨dt, h_eq, h_mem⟩ := List.maxBy_mem scalar_types.toList DType.precedence h_ne
    simp [Vector.maxBy] at h_eq
    rw [h_eq]
    rw [h_n_zero]
    simp [Vector.maxBy]
    exact ⟨dt, rfl, h_mem, fun other h_other => 
      (List.maxBy_max scalar_types.toList DType.precedence other h_other).choose_spec.2⟩
  · intro h_case3
    obtain ⟨h_n_pos, h_m_pos⟩ := h_case3
    have h_arr_ne : array_types.toList ≠ [] := by
      simp [Vector.toList_length]
      exact Nat.pos_iff_ne_zero.mp h_n_pos
    have h_scl_ne : scalar_types.toList ≠ [] := by
      simp [Vector.toList_length]
      exact Nat.pos_iff_ne_zero.mp h_m_pos
    obtain ⟨max_arr, h_arr_eq, h_arr_mem⟩ := List.maxBy_mem array_types.toList DType.precedence h_arr_ne
    obtain ⟨max_scl, h_scl_eq, h_scl_mem⟩ := List.maxBy_mem scalar_types.toList DType.precedence h_scl_ne
    simp [Vector.maxBy] at h_arr_eq h_scl_eq
    rw [h_arr_eq, h_scl_eq]
    use max_arr, max_scl
    constructor
    · exact h_arr_mem
    constructor
    · exact h_scl_mem
    constructor
    · intro dt h_dt_mem
      exact (List.maxBy_max array_types.toList DType.precedence dt h_dt_mem).choose_spec.2
    constructor
    · intro dt h_dt_mem
      exact (List.maxBy_max scalar_types.toList DType.precedence dt h_dt_mem).choose_spec.2
    · constructor
      · intro h_kind_eq
        simp [h_kind_eq]
      · intro h_kind_ne
        simp [h_kind_ne]