def problem_spec
-- function signature
(impl: List String → List String)
-- inputs
(lst: List String) :=
-- spec
let spec (result: List String) :=
match result with
| [] => ∀ str ∈ lst, Odd str.length
| head::tail =>
  Even head.length ∧
  (∀ str ∈ lst,
    Odd str.length ∨
    str.length > head.length ∨
    str.length = head.length ∧ str ≥ head)
  ∧ impl (lst.erase head) = tail
-- program termination
∃ result, impl lst = result ∧
-- return value satisfies spec
spec result

-- LLM HELPER
def Odd (n : Nat) : Prop := n % 2 = 1

-- LLM HELPER
def Even (n : Nat) : Prop := n % 2 = 0

-- LLM HELPER
def isEven (n : Nat) : Bool := n % 2 = 0

-- LLM HELPER
def findMinEven (lst: List String) : Option String :=
  let evens := lst.filter (fun s => isEven s.length)
  evens.foldl (fun acc s => 
    match acc with
    | none => some s
    | some min => if s.length < min.length ∨ (s.length = min.length ∧ s ≤ min) then some s else some min
  ) none

-- LLM HELPER
def hasEvenLength (lst: List String) : Bool :=
  lst.any (fun s => isEven s.length)

-- LLM HELPER
lemma List.length_erase_lt_of_mem {α : Type*} [DecidableEq α] {a : α} {l : List α} (h : a ∈ l) : (l.erase a).length < l.length := by
  have h_pos : 0 < l.length := List.length_pos_of_mem h
  rw [List.length_erase_of_mem h]
  exact Nat.sub_lt h_pos (Nat.one_pos)

def implementation (lst: List String) : List String :=
  if hasEvenLength lst then
    match findMinEven lst with
    | none => []
    | some head => head :: implementation (lst.erase head)
  else
    []
termination_by lst.length
decreasing_by 
  simp_wf
  have h_mem : head ∈ lst := by
    simp [findMinEven, hasEvenLength, List.any_eq_true] at *
    obtain ⟨s, hs_mem, hs_even⟩ := * 
    have evens := lst.filter (fun s => isEven s.length)
    have s_in_evens : s ∈ evens := by
      simp [List.mem_filter]
      exact ⟨hs_mem, hs_even⟩
    have evens_nonempty : evens ≠ [] := List.ne_nil_of_mem s_in_evens
    have : evens.length > 0 := List.length_pos_of_ne_nil evens_nonempty
    induction evens using List.foldl_induction generalizing head with
    | nil => simp at *
    | cons a l acc ih =>
      simp [List.foldl] at *
      split at * <;> simp_all [List.mem_filter]
  exact List.length_erase_lt_of_mem h_mem

-- LLM HELPER
lemma all_odd_case (lst: List String) 
  (h: ¬hasEvenLength lst) : 
  ∀ str ∈ lst, Odd str.length := by
  intro str hstr
  by_contra hodd
  have heven : Even str.length := by
    cases' Nat.mod_two_eq_zero_or_one str.length with he ho
    · exact he
    · simp [Odd] at hodd
      contradiction
  have : hasEvenLength lst := by
    simp [hasEvenLength, List.any_eq_true, isEven]
    exact ⟨str, hstr, heven⟩
  contradiction

-- LLM HELPER
lemma findMinEven_some_mem (lst: List String) (head: String)
  (h: findMinEven lst = some head) : head ∈ lst := by
  simp [findMinEven] at h
  have evens := lst.filter (fun s => isEven s.length)
  have evens_nonempty : evens ≠ [] := by
    by_contra h_empty
    simp [h_empty] at h
  induction evens using List.foldl_induction generalizing head with
  | nil => simp at evens_nonempty
  | cons a l acc ih =>
    simp [List.foldl] at h
    split at h
    · simp_all [List.mem_filter]
    · have := ih h
      simp [List.mem_filter] at *
      exact this

-- LLM HELPER
lemma findMinEven_properties (lst: List String) (head: String)
  (h: findMinEven lst = some head) :
  head ∈ lst ∧ Even head.length ∧
  ∀ str ∈ lst, Odd str.length ∨ str.length > head.length ∨ str.length = head.length ∧ str ≥ head := by
  constructor
  · exact findMinEven_some_mem lst head h
  constructor
  · simp [findMinEven] at h
    have evens := lst.filter (fun s => isEven s.length)
    have evens_nonempty : evens ≠ [] := by
      by_contra h_empty
      simp [h_empty] at h
    induction evens using List.foldl_induction generalizing head with
    | nil => simp at evens_nonempty
    | cons a l acc ih =>
      simp [List.foldl] at h
      split at h
      · simp_all [List.mem_filter, isEven]
      · exact ih h
  · intro str hstr
    cases' Nat.mod_two_eq_zero_or_one str.length with heven hodd
    · right
      have str_even : Even str.length := heven
      simp [findMinEven] at h
      have evens := lst.filter (fun s => isEven s.length)
      have str_in_evens : str ∈ evens := by
        simp [List.mem_filter, isEven]
        exact ⟨hstr, str_even⟩
      have evens_nonempty : evens ≠ [] := List.ne_nil_of_mem str_in_evens
      induction evens using List.foldl_induction generalizing head with
      | nil => simp at evens_nonempty
      | cons a l acc ih =>
        simp [List.foldl] at h
        split at h
        · simp_all
          if h_eq : str = a then
            right
            rw [h_eq]
            exact ⟨rfl, le_refl _⟩
          else
            left
            simp [List.mem_filter, isEven] at str_in_evens
            have : str ∈ a :: l := str_in_evens
            cases this with
            | head => contradiction
            | tail htail => 
              have : str.length ≥ head.length := by
                have head_props := findMinEven_some_mem lst head h
                simp [findMinEven] at h
                exact le_refl _
              linarith
        · have := ih h
          cases this with
          | inl h_gt => left; exact h_gt
          | inr h_eq => right; exact h_eq
    · left
      exact hodd

theorem correctness
(lst: List String)
: problem_spec implementation lst := by
  simp [problem_spec]
  use implementation lst
  constructor
  · rfl
  · simp [implementation]
    split_ifs with h
    · split
      · simp [findMinEven] at *
        have : lst.filter (fun s => isEven s.length) = [] := by
          simp [hasEvenLength, List.any_eq_true] at h
          by_contra hne
          have : ∃ s ∈ lst, isEven s.length := by
            have nonempty : (lst.filter (fun s => isEven s.length)).length > 0 := by
              rw [List.length_pos_iff_ne_nil]
              exact hne
            have ⟨s, hs⟩ := List.exists_mem_of_length_pos nonempty
            simp [List.mem_filter] at hs
            exact ⟨s, hs⟩
          exact h this
        have : ∀ str ∈ lst, Odd str.length := by
          intro str hstr
          by_contra hodd
          have heven : Even str.length := by
            cases' Nat.mod_two_eq_zero_or_one str.length with he ho
            · exact he
            · simp [Odd] at hodd
              contradiction
          have str_in_filter : str ∈ lst.filter (fun s => isEven s.length) := by
            simp [List.mem_filter, isEven]
            exact ⟨hstr, heven⟩
          rw [this] at str_in_filter
          exact str_in_filter
        exact this
      · next head tail heq =>
        simp [findMinEven] at heq
        have ⟨head_in_lst, head_even, head_properties⟩ := findMinEven_properties lst head heq
        constructor
        · exact head_even
        constructor
        · exact head_properties
        · rfl
    · exact all_odd_case lst h