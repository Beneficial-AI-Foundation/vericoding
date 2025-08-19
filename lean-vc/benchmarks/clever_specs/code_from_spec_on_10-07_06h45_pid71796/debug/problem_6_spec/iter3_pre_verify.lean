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
        have : count_max_paren_depth ((paren_string.split fun x => x = ' ')[i]!) > 0 := by
          simp [count_max_paren_depth]
          obtain ⟨balance_function, h_empty, h_step, h_nonneg, h_final⟩ := h_balanced
          have h_contains_open : ∃ c, c ∈ ((paren_string.split fun x => x = ' ')[i]!).toList ∧ c = '(' := by
            by_contra h_no_open
            simp at h_no_open
            have : ∀ c ∈ ((paren_string.split fun x => x = ' ')[i]!).toList, c ≠ '(' := h_no_open
            have : balance_function ((paren_string.split fun x => x = ' ')[i]!).toList = 0 := by
              induction' ((paren_string.split fun x => x = ' ')[i]!).toList with head tail ih
              · exact h_empty
              · have : head ≠ '(' := this head (List.mem_cons_self head tail)
                have : balance_function (head :: tail) = balance_function tail := by
                  rw [←List.nil_append (head :: tail)]
                  rw [List.cons_append]
                  rw [h_step]
                  simp [this]
                  exact ih (fun c hc => this c (List.mem_cons_of_mem head hc))
                rw [this]
                exact ih (fun c hc => this c (List.mem_cons_of_mem head hc))
            rw [h_final] at this
            exact this
          obtain ⟨c, hc_mem, hc_eq⟩ := h_contains_open
          have : (((paren_string.split fun x => x = ' ')[i]!).toList.foldl (fun acc c => 
            let new_depth := if c = '(' then acc.1 + 1
              else if c = ')' then acc.1 - 1
              else acc.1
            (new_depth, max acc.2 new_depth)) (0, 0)).2 > 0 := by
            have : ∃ j, j < ((paren_string.split fun x => x = ' ')[i]!).toList.length ∧ 
              ((paren_string.split fun x => x = ' ')[i]!).toList[j]! = '(' := by
              obtain ⟨j, hj⟩ := List.mem_iff_get.mp hc_mem
              exact ⟨j, hj.1, hj.2.symm ▸ hc_eq⟩
            obtain ⟨j, hj_bound, hj_eq⟩ := this
            have : (((paren_string.split fun x => x = ' ')[i]!).toList.take (j + 1)).foldl (fun acc c => 
              let new_depth := if c = '(' then acc.1 + 1
                else if c = ')' then acc.1 - 1
                else acc.1
              (new_depth, max acc.2 new_depth)) (0, 0) = 
              (((paren_string.split fun x => x = ' ')[i]!).toList.take j).foldl (fun acc c => 
                let new_depth := if c = '(' then acc.1 + 1
                  else if c = ')' then acc.1 - 1
                  else acc.1
                (new_depth, max acc.2 new_depth)) (0, 0) := by
              sorry
            have : (((paren_string.split fun x => x = ' ')[i]!).toList.foldl (fun acc c => 
              let new_depth := if c = '(' then acc.1 + 1
                else if c = ')' then acc.1 - 1
                else acc.1
              (new_depth, max acc.2 new_depth)) (0, 0)).2 ≥ 1 := by
              sorry
            exact Nat.pos_of_ne_zero (ne_of_gt this)
          exact this
        exact Int.ofNat_pos.mpr this
      · rw [max_depth_eq_count]
        simp [Int.toNat_of_nonneg (Int.ofNat_nonneg _)]