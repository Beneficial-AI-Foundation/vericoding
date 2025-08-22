def problem_spec
-- function signature
(implementation: List Int → Bool)
-- inputs
(arr: List Int) :=
let is_shifted (xs: List Int) (ys: List Int) (i: Nat) :=
  (xs.length = ys.length) ∧
  (0 <= i) ∧
  (i < xs.length) ∧
  (forall j, (0 <= j ∧ j < ys.length) → (ys[j]! = xs[(j-i) % xs.length]!))
-- spec
let spec (result: Bool) :=
  ((arr = []) → (result = True)) ∧
  result ↔ (exists i, exists arr_shifted, (is_shifted arr arr_shifted i) ∧ (List.Sorted Int.le arr_shifted))
-- program termination
∃ result, implementation arr = result ∧
spec result

-- LLM HELPER
def rotate_left (xs: List Int) (i: Nat) : List Int :=
  if xs.length = 0 then []
  else
    let k := i % xs.length
    xs.drop k ++ xs.take k

-- LLM HELPER
def all_rotations (xs: List Int) : List (List Int) :=
  if xs.length = 0 then [[]]
  else List.range xs.length |>.map (rotate_left xs)

-- LLM HELPER
def is_sorted (xs: List Int) : Bool :=
  match xs with
  | [] => true
  | [_] => true
  | x :: y :: rest => x <= y && is_sorted (y :: rest)

def implementation (arr: List Int) : Bool :=
  if arr = [] then true
  else (all_rotations arr).any is_sorted

-- LLM HELPER
lemma rotate_left_length (xs: List Int) (i: Nat) : (rotate_left xs i).length = xs.length := by
  simp [rotate_left]
  split
  · simp
  · simp [List.length_append, List.length_drop, List.length_take]

-- LLM HELPER
lemma rotate_left_get (xs: List Int) (i j: Nat) (h1: xs.length > 0) (h2: j < xs.length) :
  (rotate_left xs i)[j]! = xs[(j + i) % xs.length]! := by
  simp [rotate_left]
  split
  · contradiction
  · simp [List.getElem_append]
    by_cases hc : j < xs.length - i % xs.length
    · simp [hc]
      rw [List.getElem_drop]
      congr 1
      simp [Nat.add_mod]
    · simp [hc]
      rw [List.getElem_take]
      · congr 1
        have : j - (xs.length - i % xs.length) + i % xs.length = j + i % xs.length := by
          omega
        rw [this]
        simp [Nat.add_mod]
      · omega

-- LLM HELPER
lemma is_shifted_rotate_left (xs: List Int) (i: Nat) (h: xs.length > 0) :
  is_shifted xs (rotate_left xs i) i := by
  simp [is_shifted]
  constructor
  · exact rotate_left_length xs i
  constructor
  · omega
  constructor
  · omega
  · intro j hj
    have : (rotate_left xs i)[j]! = xs[(j + i) % xs.length]! := by
      apply rotate_left_get
      · exact h
      · omega
    rw [this]
    congr 1
    have : (j - i) % xs.length = (j + xs.length - i) % xs.length := by
      rw [Nat.add_sub_cancel']
      omega
    simp [Nat.add_mod, Nat.sub_mod]

-- LLM HELPER
lemma is_sorted_iff_List_Sorted (xs: List Int) : is_sorted xs ↔ List.Sorted Int.le xs := by
  induction xs with
  | nil => simp [is_sorted, List.Sorted]
  | cons x xs ih =>
    cases xs with
    | nil => simp [is_sorted, List.Sorted]
    | cons y ys =>
      simp [is_sorted, List.Sorted]
      constructor
      · intro h
        constructor
        · exact h.1
        · exact ih.mp h.2
      · intro h
        constructor
        · exact h.1
        · exact ih.mpr h.2

-- LLM HELPER
lemma all_rotations_mem (xs: List Int) (i: Nat) (h: i < xs.length) :
  rotate_left xs i ∈ all_rotations xs := by
  simp [all_rotations]
  split
  · omega
  · simp [List.mem_map]
    use i
    constructor
    · simp [List.mem_range]
      exact h
    · rfl

theorem correctness
(arr: List Int)
: problem_spec implementation arr := by
  simp [problem_spec]
  use implementation arr
  constructor
  · rfl
  · simp [implementation]
    split
    · simp
    · simp [List.any_eq_true]
      constructor
      · intro h
        obtain ⟨rot, h_mem, h_sorted⟩ := h
        simp [all_rotations] at h_mem
        split at h_mem
        · simp at h_mem
          use 0, rot
          constructor
          · simp [is_shifted]
            rw [← h_mem]
            simp
          · exact is_sorted_iff_List_Sorted.mp h_sorted
        · simp [List.mem_map] at h_mem
          obtain ⟨i, h_range, h_eq⟩ := h_mem
          use i, rot
          constructor
          · rw [← h_eq]
            apply is_shifted_rotate_left
            omega
          · exact is_sorted_iff_List_Sorted.mp h_sorted
      · intro h
        obtain ⟨i, arr_shifted, h_shifted, h_sorted⟩ := h
        use arr_shifted
        constructor
        · by_cases h_empty : arr.length = 0
          · simp [all_rotations, h_empty]
            simp [is_shifted] at h_shifted
            rw [h_shifted.1] at h_empty
            simp [h_empty]
          · have h_pos : arr.length > 0 := Nat.pos_of_ne_zero h_empty
            simp [all_rotations, h_empty]
            simp [List.mem_map]
            use i
            constructor
            · simp [List.mem_range]
              exact h_shifted.2.2.1
            · simp [is_shifted] at h_shifted
              ext j
              simp [rotate_left]
              split
              · omega
              · simp [List.getElem_append]
                by_cases hc : j < arr.length - i % arr.length
                · simp [hc]
                  rw [List.getElem_drop]
                  have : arr_shifted[j]! = arr[(j - i) % arr.length]! := h_shifted.2.2.2 j (by omega)
                  rw [this]
                  congr 1
                  simp [Nat.add_mod, Nat.sub_mod]
                · simp [hc]
                  rw [List.getElem_take]
                  · have : arr_shifted[j]! = arr[(j - i) % arr.length]! := h_shifted.2.2.2 j (by omega)
                    rw [this]
                    congr 1
                    simp [Nat.add_mod, Nat.sub_mod]
                  · omega
        · exact is_sorted_iff_List_Sorted.mpr h_sorted