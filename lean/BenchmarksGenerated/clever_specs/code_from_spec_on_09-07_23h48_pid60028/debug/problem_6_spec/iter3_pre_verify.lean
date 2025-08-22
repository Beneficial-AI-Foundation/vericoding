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
lemma compute_depth_pos (group: String) (h: balanced_paren_non_computable group '(' ')') : 
  0 < compute_depth group := by
  unfold compute_depth
  simp [Int.ofNat_pos]
  unfold count_max_paren_depth
  cases' h with depth hd
  have h_contains_parens : ∃ i, i < group.length ∧ group.get ⟨i, by assumption⟩ = '(' := by
    by_cases h_empty : group.length = 0
    · exfalso
      simp [h_empty] at hd
      have := hd.2
      simp at this
      cases' this with h_eq
      contradiction
    · push_neg at h_empty
      have h_nonzero : 0 < group.length := Nat.pos_of_ne_zero h_empty
      use 0
      constructor
      · exact h_nonzero
      · have := hd.1 0 h_nonzero
        cases' this with h_open h_rest
        · exact h_open
        · cases' h_rest with h_close h_neither
          · exfalso
            have h_fold := hd.2
            simp at h_fold
            have h_some_open : ∃ i, i < group.length ∧ group.get ⟨i, by assumption⟩ = '(' := by
              by_contra h_no_open
              push_neg at h_no_open
              have h_all_close_or_other : ∀ i, i < group.length → group.get ⟨i, by assumption⟩ = ')' ∨ (group.get ⟨i, by assumption⟩ ≠ '(' ∧ group.get ⟨i, by assumption⟩ ≠ ')') := by
                intro i hi
                have := hd.1 i hi
                cases' this with h_open h_rest
                · exfalso
                  exact h_no_open i hi h_open
                · exact h_rest
              contradiction
            exact h_some_open
          · exfalso
            have h_fold := hd.2
            simp at h_fold
            have h_some_open : ∃ i, i < group.length ∧ group.get ⟨i, by assumption⟩ = '(' := by
              by_contra h_no_open
              push_neg at h_no_open
              have h_all_close_or_other : ∀ i, i < group.length → group.get ⟨i, by assumption⟩ = ')' ∨ (group.get ⟨i, by assumption⟩ ≠ '(' ∧ group.get ⟨i, by assumption⟩ ≠ ')') := by
                intro i hi
                have := hd.1 i hi
                cases' this with h_open h_rest
                · exfalso
                  exact h_no_open i hi h_open
                · exact h_rest
              contradiction
            exact h_some_open
  cases' h_contains_parens with i hi
  have h_pos : 0 < count_max_paren_depth group := by
    unfold count_max_paren_depth
    simp
    apply Nat.pos_of_ne_zero
    intro h_zero
    have h_fold := group.toList.foldl (fun acc c => let (curr_depth, max_depth) := acc; if c = '(' then let new_depth := curr_depth + 1; (new_depth, max (new_depth) max_depth) else if c = ')' then (curr_depth - 1, max_depth) else acc) (0, 0)
    have h_max_zero : h_fold.2 = 0 := h_zero
    contradiction
  exact h_pos

-- LLM HELPER
lemma compute_depth_correct (group: String) :
  count_max_paren_depth group = (compute_depth group).toNat := by
  unfold compute_depth
  simp [Int.toNat_of_nonneg]

-- LLM HELPER
lemma list_map_length {α β : Type*} (f : α → β) (l : List α) : 
  (l.map f).length = l.length := by
  induction l with
  | nil => simp
  | cons h t ih => simp [ih]

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
      intro group_def h_balanced
      rw [List.get_map]
      constructor
      · exact compute_depth_pos _ h_balanced
      · exact compute_depth_correct _