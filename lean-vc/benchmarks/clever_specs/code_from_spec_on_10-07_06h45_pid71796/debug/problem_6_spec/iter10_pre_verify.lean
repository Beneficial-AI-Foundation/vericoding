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
def balanced_paren_non_computable (s: String) (open_char close_char: Char) : Prop :=
∃ balance_function : List Char → Int,
let chars := s.toList;
balance_function [] = 0 ∧
∀ cs c, balance_function (cs ++ [c]) = 
  if c = open_char then balance_function cs + 1
  else if c = close_char then balance_function cs - 1
  else balance_function cs ∧
(∀ prefix, prefix.isPrefixOf chars → balance_function prefix ≥ 0) ∧
balance_function chars = 0

-- LLM HELPER
def count_max_paren_depth (s: String) : Nat :=
let chars := s.toList
let depths := chars.foldl (fun acc c => 
  let new_depth := if c = '(' then acc.1 + 1
    else if c = ')' then acc.1 - 1
    else acc.1
  (new_depth, max acc.2 new_depth)) (0, 0)
depths.2

-- LLM HELPER
def max_depth_single_group (s: String) : Int :=
let chars := s.toList
let depths := chars.foldl (fun acc c => 
  let new_depth := if c = '(' then acc.1 + 1
    else if c = ')' then acc.1 - 1
    else acc.1
  (new_depth, max acc.2 new_depth)) (0, 0)
Int.ofNat depths.2

-- LLM HELPER
lemma max_depth_eq_count (s: String) : 
  max_depth_single_group s = Int.ofNat (count_max_paren_depth s) := by
  simp [max_depth_single_group, count_max_paren_depth]

-- LLM HELPER
lemma count_max_paren_depth_pos_of_balanced (s: String) : 
  balanced_paren_non_computable s '(' ')' → s ≠ "" → count_max_paren_depth s > 0 := by
  intro h_balanced h_nonempty
  obtain ⟨balance_function, h_base, h_step, h_prefix, h_final⟩ := h_balanced
  simp [count_max_paren_depth]
  by_contra h_contra
  push_neg at h_contra
  have h_zero : count_max_paren_depth s = 0 := Nat.eq_zero_of_le_zero h_contra
  simp [count_max_paren_depth] at h_zero
  cases' s.toList with c cs
  · simp at h_nonempty
  · simp at h_zero
    have : ∃ c ∈ (c :: cs), c = '(' ∨ c = ')' := by
      by_contra h_no_parens
      push_neg at h_no_parens
      have h_all_other : ∀ x ∈ (c :: cs), x ≠ '(' ∧ x ≠ ')' := h_no_parens
      have h_balance_zero : balance_function (c :: cs) = 0 := by
        induction cs generalizing c with
        | nil => 
          have h_not_paren := h_all_other c (List.mem_singleton.mpr rfl)
          rw [h_step]
          simp [h_not_paren.1, h_not_paren.2, h_base]
        | cons d ds ih =>
          rw [h_step]
          have h_not_paren := h_all_other c (List.mem_cons_self c (d :: ds))
          simp [h_not_paren.1, h_not_paren.2]
          exact ih d (fun x hx => h_all_other x (List.mem_cons_of_mem c hx))
      rw [h_final] at h_balance_zero
      exact h_balance_zero
    obtain ⟨x, hx_mem, hx_paren⟩ := this
    cases' hx_paren with h_open h_close
    · by_contra
      exact h_zero
    · by_contra
      exact h_zero

def implementation (paren_string: String) : List Int := 
let groups := paren_string.split (fun x => x = ' ')
groups.map max_depth_single_group

theorem correctness
(paren_string: String)
: problem_spec implementation paren_string
:= by
  use (paren_string.split (fun x => x = ' ')).map max_depth_single_group
  constructor
  · rfl
  · constructor
    · simp [implementation]
    · intro i hi
      simp [implementation] at hi ⊢
      intro h_balanced
      constructor
      · simp [max_depth_single_group]
        by_cases h_empty : (paren_string.split (fun x => x = ' '))[i]! = ""
        · simp [h_empty, count_max_paren_depth]
          exact Int.ofNat_pos.mpr (Nat.zero_lt_one)
        · exact Int.ofNat_pos.mpr (count_max_paren_depth_pos_of_balanced _ h_balanced h_empty)
      · rw [max_depth_eq_count]
        simp [Int.toNat_of_nonneg (Int.ofNat_nonneg _)]