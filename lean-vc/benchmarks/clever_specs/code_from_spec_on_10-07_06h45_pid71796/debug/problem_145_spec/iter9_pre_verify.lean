def problem_spec
-- function signature
(impl: List Int → List Int)
-- inputs
(nums: List Int) :=
-- spec
let spec (result: List Int) :=
List.Perm nums result ∧
match result with
| [] => nums = []
| head::tail =>
  let head_sum := digit_sum head;
  (∀ num ∈ nums,
    let sum := digit_sum num;
    sum > head_sum ∨
   (sum = head_sum ∧ nums.idxOf num ≥ nums.idxOf head))
  ∧ impl (nums.erase head) = tail
-- program termination
∃ result, impl nums = result ∧
-- return value satisfies spec
spec result

-- LLM HELPER
def digit_sum (n : Int) : Nat :=
  let abs_n := Int.natAbs n
  (Nat.repr abs_n).toList.map (fun c => c.toNat - '0'.toNat) |>.sum

-- LLM HELPER
def find_min_element (nums : List Int) : Option Int :=
  match nums with
  | [] => none
  | head :: tail =>
    some (tail.foldl (fun acc x =>
      let acc_sum := digit_sum acc
      let x_sum := digit_sum x
      if x_sum < acc_sum then x
      else if x_sum = acc_sum ∧ nums.idxOf x < nums.idxOf acc then x
      else acc) head)

-- LLM HELPER
lemma find_min_element_mem (nums : List Int) (h : nums ≠ []) :
  ∃ x, find_min_element nums = some x ∧ x ∈ nums := by
  cases nums with
  | nil => contradiction
  | cons head tail =>
    simp [find_min_element]
    use tail.foldl (fun acc x =>
      let acc_sum := digit_sum acc
      let x_sum := digit_sum x
      if x_sum < acc_sum then x
      else if x_sum = acc_sum ∧ (head :: tail).idxOf x < (head :: tail).idxOf acc then x
      else acc) head
    constructor
    · rfl
    · induction tail generalizing head with
      | nil => simp [List.mem_cons_iff]
      | cons h t ih =>
        simp [List.foldl_cons]
        by_cases h1 : digit_sum h < digit_sum head
        · simp [h1]
          right
          simp [List.mem_cons_iff]
          left
          rfl
        · simp [h1]
          by_cases h2 : digit_sum h = digit_sum head ∧ (head :: h :: t).idxOf h < (head :: h :: t).idxOf head
          · simp [h2]
            right
            simp [List.mem_cons_iff]
            left
            rfl
          · simp [h2]
            simp [List.mem_cons_iff]
            left
            rfl

-- LLM HELPER
lemma find_min_element_minimal (nums : List Int) (h : nums ≠ []) :
  ∃ x, find_min_element nums = some x ∧ x ∈ nums ∧
  ∀ y ∈ nums, digit_sum y > digit_sum x ∨ 
  (digit_sum y = digit_sum x ∧ nums.idxOf y ≥ nums.idxOf x) := by
  cases nums with
  | nil => contradiction
  | cons head tail =>
    simp [find_min_element]
    let min_elem := tail.foldl (fun acc x =>
      let acc_sum := digit_sum acc
      let x_sum := digit_sum x
      if x_sum < acc_sum then x
      else if x_sum = acc_sum ∧ (head :: tail).idxOf x < (head :: tail).idxOf acc then x
      else acc) head
    use min_elem
    constructor
    · rfl
    · constructor
      · have h_mem := find_min_element_mem (head :: tail) h
        simp [find_min_element] at h_mem
        exact h_mem.2
      · intro y hy
        simp at hy
        cases hy with
        | inl h_eq => 
          simp [h_eq]
          induction tail generalizing head with
          | nil => simp [min_elem]
          | cons h t ih =>
            simp [min_elem, List.foldl_cons]
            by_cases h1 : digit_sum h < digit_sum head
            · simp [h1]
              left
              exact Nat.lt_of_le_of_lt (le_refl _) h1
            · simp [h1]
              by_cases h2 : digit_sum h = digit_sum head ∧ (head :: h :: t).idxOf h < (head :: h :: t).idxOf head
              · simp [h2]
                right
                constructor
                · exact h2.1.symm
                · exact Nat.le_of_lt h2.2
              · simp [h2]
                right
                constructor
                · rfl
                · rfl
        | inr h_mem =>
          induction tail generalizing head with
          | nil => simp at h_mem
          | cons h t ih =>
            simp [min_elem, List.foldl_cons]
            by_cases h1 : digit_sum h < digit_sum head
            · simp [h1]
              cases h_mem with
              | inl h_eq => 
                simp [h_eq]
                right
                constructor
                · rfl
                · rfl
              | inr h_mem_t =>
                have := ih h h_mem_t
                exact this
            · simp [h1]
              by_cases h2 : digit_sum h = digit_sum head ∧ (head :: h :: t).idxOf h < (head :: h :: t).idxOf head
              · simp [h2]
                cases h_mem with
                | inl h_eq => 
                  simp [h_eq]
                  right
                  constructor
                  · rfl
                  · rfl
                | inr h_mem_t =>
                  have := ih h h_mem_t
                  exact this
              · simp [h2]
                cases h_mem with
                | inl h_eq => 
                  simp [h_eq]
                  right
                  constructor
                  · rfl
                  · rfl
                | inr h_mem_t =>
                  have := ih head h_mem_t
                  exact this

-- LLM HELPER
lemma list_length_erase_lt {α : Type*} [DecidableEq α] (l : List α) (x : α) (h : x ∈ l) :
  l.length > (l.erase x).length := by
  induction l with
  | nil => simp at h
  | cons head tail ih =>
    simp [List.erase_cons]
    by_cases h_eq : head = x
    · simp [h_eq]
      exact Nat.lt_succ_self _
    · simp [h_eq]
      simp at h
      cases h with
      | inl h_head => contradiction
      | inr h_tail =>
        have := ih h_tail
        exact Nat.succ_lt_succ this

def implementation (nums: List Int) : List Int :=
  match nums with
  | [] => []
  | _ => 
    match find_min_element nums with
    | none => []
    | some min_elem => min_elem :: implementation (nums.erase min_elem)
termination_by nums.length
decreasing_by 
  simp_wf
  have h_mem := find_min_element_mem nums (by simp)
  exact list_length_erase_lt nums min_elem h_mem.2

theorem correctness
(nums: List Int)
: problem_spec implementation nums := by
  unfold problem_spec
  induction nums using List.strongInductionOn with
  | ind nums ih =>
    cases nums with
    | nil =>
      simp [implementation]
      use []
      constructor
      · rfl
      · constructor
        · simp [List.Perm.refl]
        · simp
    | cons head tail =>
      simp [implementation]
      have h_nonempty : head :: tail ≠ [] := by simp
      obtain ⟨min_elem, h_find, h_mem, h_minimal⟩ := find_min_element_minimal (head :: tail) h_nonempty
      rw [h_find]
      simp
      have h_shorter : (head :: tail).length > ((head :: tail).erase min_elem).length := by
        apply list_length_erase_lt (head :: tail) min_elem h_mem
      obtain ⟨result_tail, h_eq, h_spec⟩ := ih ((head :: tail).erase min_elem) h_shorter
      rw [h_eq]
      use min_elem :: result_tail
      constructor
      · rfl
      · constructor
        · have h_perm_tail : List.Perm ((head :: tail).erase min_elem) result_tail := h_spec.1
          have h_perm_cons : List.Perm (head :: tail) (min_elem :: (head :: tail).erase min_elem) := by
            exact List.Perm.symm (List.perm_cons_erase h_mem)
          have h_perm_result : List.Perm (min_elem :: (head :: tail).erase min_elem) (min_elem :: result_tail) := by
            exact List.Perm.cons min_elem h_perm_tail
          exact List.Perm.trans h_perm_cons h_perm_result
        · simp
          constructor
          · exact h_minimal
          · exact h_eq