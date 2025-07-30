def problem_spec
-- function signature
(implementation: String → List Int)
-- inputs
(paren_string: String)
:=
-- spec
let spec (result: List Int) :=
let paren_space_split := paren_string.split (fun x => x = ' ');
result.length = paren_space_split.length ∧
∀ i, i < result.length →
let group := paren_space_split[i]!;
balanced_paren_non_computable group '(' ')' →
0 < result[i]! ∧ count_max_paren_depth group = result[i]!.toNat;
-- program termination
∃ result, implementation paren_string = result ∧
spec result

-- LLM HELPER
def balanced_paren_non_computable (s: String) (open: Char) (close: Char) : Prop :=
∃ (depth: Nat), 
  (∀ i, i < s.length → 
    let c := s.get ⟨i, by assumption⟩
    c = open ∨ c = close ∨ (c ≠ open ∧ c ≠ close)) ∧
  (s.toList.foldl (fun acc c => 
    if c = open then acc + 1 
    else if c = close then acc - 1 
    else acc) 0 = 0)

-- LLM HELPER
def count_max_paren_depth (s: String) : Nat :=
s.toList.foldl (fun acc c => 
  let (curr_depth, max_depth) := acc
  if c = '(' then 
    let new_depth := curr_depth + 1
    (new_depth, max (new_depth) max_depth)
  else if c = ')' then 
    (curr_depth - 1, max_depth)
  else 
    acc) (0, 0) |>.2

-- LLM HELPER
def compute_depth (group: String) : Int :=
Int.ofNat (count_max_paren_depth group)

def implementation (paren_string: String) : List Int := 
let paren_space_split := paren_string.split (fun x => x = ' ')
paren_space_split.map compute_depth

-- LLM HELPER
lemma list_map_length {α β : Type*} (f : α → β) (l : List α) : 
  (l.map f).length = l.length := by
  induction l with
  | nil => simp
  | cons h t ih => simp [ih]

-- LLM HELPER
lemma count_max_paren_depth_pos (s: String) : 
  (s.toList.any (fun c => c = '(')) → 0 < count_max_paren_depth s := by
  intro h
  unfold count_max_paren_depth
  simp
  have : ∃ i, i < s.length ∧ s.get ⟨i, by assumption⟩ = '(' := by
    rw [List.any_eq_true] at h
    obtain ⟨c, hc_mem, hc_eq⟩ := h
    rw [String.mem_toList] at hc_mem
    exact ⟨_, hc_mem, hc_eq⟩
  obtain ⟨i, hi, hget⟩ := this
  apply Nat.zero_lt_of_ne_zero
  intro h_eq
  have h_all_zero : ∀ j, j < s.length → s.get ⟨j, by assumption⟩ ≠ '(' := by
    intro j hj
    by_contra h_contra
    have : 0 < count_max_paren_depth s := by
      unfold count_max_paren_depth
      simp
      use j
      exact ⟨hj, h_contra⟩
    rw [h_eq] at this
    exact Nat.lt_irrefl 0 this
  exact h_all_zero i hi hget

theorem correctness
(paren_string: String)
: problem_spec implementation paren_string := by
  unfold problem_spec
  use (paren_string.split (fun x => x = ' ')).map compute_depth
  constructor
  · rfl
  · constructor
    · simp [implementation]
      exact list_map_length compute_depth (paren_string.split (fun x => x = ' '))
    · intro i hi
      simp [implementation] at hi
      intro h_balanced
      rw [List.get_map]
      constructor
      · unfold compute_depth
        simp [Int.ofNat_pos]
        unfold count_max_paren_depth
        simp
        obtain ⟨depth, h_chars, h_balanced_fold⟩ := h_balanced
        by_cases h_has_open : (paren_string.split (fun x => x = ' '))[i]!.toList.any (fun c => c = '(')
        · exact count_max_paren_depth_pos (paren_string.split (fun x => x = ' '))[i]! h_has_open
        · simp at h_has_open
          have h_no_open : ∀ c ∈ (paren_string.split (fun x => x = ' '))[i]!.toList, c ≠ '(' := by
            intro c hc
            rw [List.any_eq_false] at h_has_open
            exact h_has_open c hc
          have h_no_close : ∀ c ∈ (paren_string.split (fun x => x = ' '))[i]!.toList, c ≠ ')' := by
            intro c hc
            by_contra h_contra
            have h_pos : 0 < count_max_paren_depth (paren_string.split (fun x => x = ' '))[i]! := by
              unfold count_max_paren_depth
              simp
              use c
              exact ⟨hc, h_contra⟩
            contradiction
          have h_empty : (paren_string.split (fun x => x = ' '))[i]! = "" := by
            by_contra h_ne_empty
            obtain ⟨c, hc⟩ := String.exists_mem_of_ne_empty h_ne_empty
            rw [String.mem_toList] at hc
            have h_not_open := h_no_open c hc
            have h_not_close := h_no_close c hc
            obtain ⟨_, h_char_prop, _⟩ := h_balanced
            have h_char := h_char_prop (String.toList (paren_string.split (fun x => x = ' '))[i]!).indexOf c
            simp at h_char
            exact h_char h_not_open h_not_close
          rw [h_empty]
          simp [count_max_paren_depth]
      · unfold compute_depth
        simp [Int.toNat_of_nonneg]
        rfl