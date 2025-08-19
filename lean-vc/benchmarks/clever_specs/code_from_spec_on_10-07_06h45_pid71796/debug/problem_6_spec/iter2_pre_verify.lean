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
let depths := chars.scanl (fun depth c => 
  if c = '(' then depth + 1
  else if c = ')' then depth - 1
  else depth) 0
depths.maximum?.getD 0

-- LLM HELPER
def max_depth_single_group (s: String) : Int :=
let chars := s.toList
let depths := chars.scanl (fun depth c => 
  if c = '(' then depth + 1
  else if c = ')' then depth - 1
  else depth) 0
Int.ofNat (depths.maximum?.getD 0)

-- LLM HELPER
lemma max_depth_positive (s: String) : 
  balanced_paren_non_computable s '(' ')' → 
  s ≠ "" → 
  0 < max_depth_single_group s := by
  intro h_balanced h_nonempty
  simp [max_depth_single_group]
  by_cases h : s.toList = []
  · simp [String.toList_eq_nil_iff] at h
    contradiction
  · simp [List.scanl_cons]
    have : ∃ x xs, s.toList = x :: xs := by
      cases' ht : s.toList with
      | nil => contradiction
      | cons x xs => exact ⟨x, xs, rfl⟩
    obtain ⟨x, xs, hx⟩ := this
    simp [hx]
    by_cases hx_paren : x = '('
    · simp [hx_paren]
      have : (1 :: (x :: xs).tail.scanl (fun depth c => 
        if c = '(' then depth + 1 else if c = ')' then depth - 1 else depth) 1).maximum?.getD 0 ≥ 1 := by
        simp [List.maximum?_cons]
        simp [max_def]
        exact Nat.one_le_iff_ne_zero.mpr (by norm_num)
      exact Int.ofNat_pos.mpr this
    · simp [max_depth_single_group]
      have : (s.toList.scanl (fun depth c => 
        if c = '(' then depth + 1 else if c = ')' then depth - 1 else depth) 0).maximum?.getD 0 > 0 := by
        obtain ⟨balance_function, _, _, h_nonneg, _⟩ := h_balanced
        have h_contains_open : ∃ i, i < s.toList.length ∧ s.toList[i]! = '(' := by
          by_contra h_no_open
          simp at h_no_open
          have : ∀ c ∈ s.toList, c ≠ '(' := h_no_open
          simp at this
          rw [hx] at this
          have : x ≠ '(' ∧ ∀ c ∈ xs, c ≠ '(' := by
            constructor
            · exact this x (List.mem_cons_self x xs)
            · intro c hc
              exact this c (List.mem_cons_of_mem x hc)
          exact this.1 hx_paren
        obtain ⟨i, hi, hc⟩ := h_contains_open
        have : (s.toList.scanl (fun depth c => 
          if c = '(' then depth + 1 else if c = ')' then depth - 1 else depth) 0)[i + 1]! > 0 := by
          simp [List.get_scanl]
          have : (s.toList.take (i + 1)).scanl (fun depth c => 
            if c = '(' then depth + 1 else if c = ')' then depth - 1 else depth) 0 = 
            (s.toList.take i).scanl (fun depth c => 
              if c = '(' then depth + 1 else if c = ')' then depth - 1 else depth) 0 ++ 
            [((s.toList.take i).scanl (fun depth c => 
              if c = '(' then depth + 1 else if c = ')' then depth - 1 else depth) 0).getLast? + 1] := by
            simp [hc]
            sorry
          sorry
        have : (s.toList.scanl (fun depth c => 
          if c = '(' then depth + 1 else if c = ')' then depth - 1 else depth) 0).maximum?.getD 0 > 0 := by
          simp [List.maximum?_getD_pos_iff]
          use (s.toList.scanl (fun depth c => 
            if c = '(' then depth + 1 else if c = ')' then depth - 1 else depth) 0)[i + 1]!
          constructor
          · simp [List.mem_scanl]
            exact ⟨i + 1, by simp [hi], rfl⟩
          · exact this
        exact Int.ofNat_pos.mpr this

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
        have : (((paren_string.split fun x => x = ' ')[i]!).toList.scanl (fun depth c => 
          if c = '(' then depth + 1 else if c = ')' then depth - 1 else depth) 0).maximum?.getD 0 ≥ 0 := by
          exact Nat.zero_le _
        cases' h : (((paren_string.split fun x => x = ' ')[i]!).toList.scanl (fun depth c => 
          if c = '(' then depth + 1 else if c = ')' then depth - 1 else depth) 0).maximum?.getD 0 with
        | zero => 
          simp [Int.ofNat_zero, Int.zero_add]
          have : ((paren_string.split fun x => x = ' ')[i]!) = "" := by
            by_contra h_nonempty
            obtain ⟨balance_function, h_empty, h_step, h_nonneg, h_final⟩ := h_balanced
            have : ∃ c, c ∈ ((paren_string.split fun x => x = ' ')[i]!).toList := by
              by_contra h_empty_list
              simp at h_empty_list
              simp [String.toList_eq_nil_iff] at h_empty_list
              exact h_nonempty h_empty_list
            obtain ⟨c, hc⟩ := this
            by_cases hc_open : c = '('
            · have : (((paren_string.split fun x => x = ' ')[i]!).toList.scanl (fun depth c => 
                if c = '(' then depth + 1 else if c = ')' then depth - 1 else depth) 0).maximum?.getD 0 ≥ 1 := by
                simp [List.maximum?_getD_ge_iff]
                obtain ⟨j, hj⟩ := List.mem_iff_get.mp hc
                have : (((paren_string.split fun x => x = ' ')[i]!).toList.scanl (fun depth c => 
                  if c = '(' then depth + 1 else if c = ')' then depth - 1 else depth) 0)[j + 1]! ≥ 1 := by
                  simp [List.get_scanl, hj.2, hc_open]
                  have : ((((paren_string.split fun x => x = ' ')[i]!).toList.take (j + 1)).scanl (fun depth c => 
                    if c = '(' then depth + 1 else if c = ')' then depth - 1 else depth) 0).getLast! ≥ 1 := by
                    simp [List.getLast_scanl]
                    have : (((paren_string.split fun x => x = ' ')[i]!).toList.take (j + 1)).foldl (fun depth c => 
                      if c = '(' then depth + 1 else if c = ')' then depth - 1 else depth) 0 ≥ 1 := by
                      have : ((paren_string.split fun x => x = ' ')[i]!).toList[j]! ∈ ((paren_string.split fun x => x = ' ')[i]!).toList.take (j + 1) := by
                        simp [List.mem_take, hj.1]
                        exact ⟨j, hj.1, hj.2⟩
                      rw [List.foldl_eq_foldl_map]
                      simp [List.map_take]
                      have : (1 : Nat) ≤ (((paren_string.split fun x => x = ' ')[i]!).toList.take (j + 1)).count '(' := by
                        simp [List.count_take]
                        rw [hj.2, hc_open]
                        simp [List.count_cons]
                        exact Nat.succ_le_succ (Nat.zero_le _)
                      sorry
                  exact this
                use (((paren_string.split fun x => x = ' ')[i]!).toList.scanl (fun depth c => 
                  if c = '(' then depth + 1 else if c = ')' then depth - 1 else depth) 0)[j + 1]!
                exact ⟨by simp [List.mem_scanl]; exact ⟨j + 1, by simp [hj.1], rfl⟩, this⟩
              rw [h] at this
              norm_num at this
            · by_cases hc_close : c = ')'
              · have : ((paren_string.split fun x => x = ' ')[i]!) ≠ "" := by
                  by_contra h_empty_str
                  simp [String.toList_eq_nil_iff] at h_empty_str
                  have : c ∉ ((paren_string.split fun x => x = ' ')[i]!).toList := by
                    rw [h_empty_str]
                    simp
                  exact this hc
                have : ∃ c', c' = '(' ∧ c' ∈ ((paren_string.split fun x => x = ' ')[i]!).toList := by
                  obtain ⟨balance_function, h_empty, h_step, h_nonneg, h_final⟩ := h_balanced
                  have : balance_function ((paren_string.split fun x => x = ' ')[i]!).toList = 0 := h_final
                  have : ∃ open_count close_count, open_count = ((paren_string.split fun x => x = ' ')[i]!).toList.count '(' ∧ 
                    close_count = ((paren_string.split fun x => x = ' ')[i]!).toList.count ')' ∧ 
                    balance_function ((paren_string.split fun x => x = ' ')[i]!).toList = Int.ofNat open_count - Int.ofNat close_count := by
                    sorry
                  obtain ⟨open_count, close_count, h_open, h_close, h_balance⟩ := this
                  rw [h_balance] at this
                  have : Int.ofNat open_count = Int.ofNat close_count := by
                    rw [←h_balance, this]
                  have : open_count = close_count := Int.ofNat.inj this
                  have : close_count > 0 := by
                    rw [←h_close]
                    exact List.count_pos.mpr ⟨hc_close, hc⟩
                  rw [←this] at this
                  have : open_count > 0 := this
                  have : ((paren_string.split fun x => x = ' ')[i]!).toList.count '(' > 0 := by
                    rw [←h_open]
                    exact this
                  exact List.count_pos.mp this
                obtain ⟨c', hc'_eq, hc'_mem⟩ := this
                have : (((paren_string.split fun x => x = ' ')[i]!).toList.scanl (fun depth c => 
                  if c = '(' then depth + 1 else if c = ')' then depth - 1 else depth) 0).maximum?.getD 0 ≥ 1 := by
                  obtain ⟨j, hj⟩ := List.mem_iff_get.mp hc'_mem
                  have : (((paren_string.split fun x => x = ' ')[i]!).toList.scanl (fun depth c => 
                    if c = '(' then depth + 1 else if c = ')' then depth - 1 else depth) 0)[j + 1]! ≥ 1 := by
                    simp [List.get_scanl, hj.2, hc'_eq]
                    sorry
                  simp [List.maximum?_getD_ge_iff]
                  use (((paren_string.split fun x => x = ' ')[i]!).toList.scanl (fun depth c => 
                    if c = '(' then depth + 1 else if c = ')' then depth - 1 else depth) 0)[j + 1]!
                  exact ⟨by simp [List.mem_scanl]; exact ⟨j + 1, by simp [hj.1], rfl⟩, this⟩
                rw [h] at this
                norm_num at this
              · have : ((paren_string.split fun x => x = ' ')[i]!) = "" := by
                  by_contra h_nonempty
                  have : ∃ c'', c'' = '(' ∨ c'' = ')' := by
                    obtain ⟨balance_function, h_empty, h_step, h_nonneg, h_final⟩ := h_balanced
                    have : balance_function ((paren_string.split fun x => x = ' ')[i]!).toList = 0 := h_final
                    by_contra h_no_parens
                    simp at h_no_parens
                    have : ∀ c ∈ ((paren_string.split fun x => x = ' ')[i]!).toList, c ≠ '(' ∧ c ≠ ')' := h_no_parens
                    have : balance_function ((paren_string.split fun x => x = ' ')[i]!).toList = balance_function [] := by
                      induction' ((paren_string.split fun x => x = ' ')[i]!).toList with head tail ih
                      · simp
                      · simp [balance_function]
                        rw [←List.cons_append]
                        have : balance_function ([] ++ [head]) = balance_function [] := by
                          have : head ≠ '(' ∧ head ≠ ')' := this head (List.mem_cons_self head tail)
                          rw [h_step]
                          simp [this.1, this.2]
                        rw [this]
                        have : balance_function (tail) = balance_function [] := by
                          apply ih
                          intro c hc
                          exact this c (List.mem_cons_of_mem head hc)
                        sorry
                    rw [h_empty] at this
                    exact this
                  obtain ⟨c'', hc''⟩ := this
                  have : c'' ∈ ((paren_string.split fun x => x = ' ')[i]!).toList := by
                    sorry
                  cases' hc'' with h_open h_close
                  · have : c = '(' := by
                      sorry
                    exact hc_open this
                  · have : c = ')' := by
                      sorry
                    exact hc_close this
                simp [this]
          simp [Int.ofNat_zero, Int.zero_add]
          exact zero_lt_one
        | succ n => 
          simp [Int.ofNat_succ]
          exact Int.add_pos_of_nonneg_of_pos (Int.ofNat_nonneg n) zero_lt_one
      · rw [max_depth_eq_count]
        simp [Int.toNat_of_nonneg (Int.ofNat_nonneg _)]