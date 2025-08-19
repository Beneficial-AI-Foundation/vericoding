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

-- LLM HELPER
lemma findMinEven_mem_of_hasEvenLength (lst: List String) (h: hasEvenLength lst) : 
  ∃ s, findMinEven lst = some s ∧ s ∈ lst := by
  simp [hasEvenLength, List.any_eq_true, isEven] at h
  obtain ⟨s, hs_mem, hs_even⟩ := h
  simp [findMinEven]
  let evens := lst.filter (fun s => isEven s.length)
  have s_in_evens : s ∈ evens := by
    simp [List.mem_filter, isEven]
    exact ⟨hs_mem, hs_even⟩
  have evens_nonempty : evens ≠ [] := List.ne_nil_of_mem s_in_evens
  cases' evens with head tail
  · contradiction
  · simp [List.foldl]
    use head
    constructor
    · induction tail with
      | nil => simp
      | cons a as ih => 
        simp [List.foldl]
        split_ifs <;> simp
    · have head_in_lst : head ∈ lst := by
        have : head ∈ evens := List.mem_cons_self head tail
        simp [List.mem_filter] at this
        exact this.1
      exact head_in_lst

def implementation (lst: List String) : List String :=
  if h : hasEvenLength lst then
    match h' : findMinEven lst with
    | none => []
    | some head => 
      have head_mem : head ∈ lst := by
        have ⟨s, hs_eq, hs_mem⟩ := findMinEven_mem_of_hasEvenLength lst h
        rw [hs_eq] at h'
        simp at h'
        rw [h']
        exact hs_mem
      head :: implementation (lst.erase head)
  else
    []
termination_by lst.length
decreasing_by 
  simp_wf
  exact List.length_erase_lt_of_mem head_mem

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
  let evens := lst.filter (fun s => isEven s.length)
  have evens_nonempty : evens ≠ [] := by
    by_contra h_empty
    simp [h_empty] at h
  cases' evens with first rest
  · contradiction
  · simp [List.foldl] at h
    induction rest generalizing head first with
    | nil => 
      simp at h
      rw [h]
      have : first ∈ evens := List.mem_cons_self first []
      simp [List.mem_filter] at this
      exact this.1
    | cons a as ih =>
      simp [List.foldl] at h
      split at h
      · have : head = a := by simp_all
        rw [this]
        have : a ∈ evens := List.mem_cons_of_mem first (List.mem_cons_self a as)
        simp [List.mem_filter] at this
        exact this.1
      · have : head = first := by simp_all
        rw [this]
        have : first ∈ evens := List.mem_cons_self first (a :: as)
        simp [List.mem_filter] at this
        exact this.1

-- LLM HELPER
lemma findMinEven_properties (lst: List String) (head: String)
  (h: findMinEven lst = some head) :
  head ∈ lst ∧ Even head.length ∧
  ∀ str ∈ lst, Odd str.length ∨ str.length > head.length ∨ str.length = head.length ∧ str ≥ head := by
  constructor
  · exact findMinEven_some_mem lst head h
  constructor
  · simp [findMinEven] at h
    let evens := lst.filter (fun s => isEven s.length)
    have evens_nonempty : evens ≠ [] := by
      by_contra h_empty
      simp [h_empty] at h
    cases' evens with first rest
    · contradiction
    · simp [List.foldl] at h
      induction rest generalizing head first with
      | nil => 
        simp at h
        rw [h]
        have : first ∈ evens := List.mem_cons_self first []
        simp [List.mem_filter, isEven] at this
        exact this.2
      | cons a as ih =>
        simp [List.foldl] at h
        split at h
        · have : head = a := by simp_all
          rw [this]
          have : a ∈ evens := List.mem_cons_of_mem first (List.mem_cons_self a as)
          simp [List.mem_filter, isEven] at this
          exact this.2
        · have : head = first := by simp_all
          rw [this]
          have : first ∈ evens := List.mem_cons_self first (a :: as)
          simp [List.mem_filter, isEven] at this
          exact this.2
  · intro str hstr
    cases' Nat.mod_two_eq_zero_or_one str.length with heven hodd
    · right
      have str_even : Even str.length := heven
      simp [findMinEven] at h
      let evens := lst.filter (fun s => isEven s.length)
      have str_in_evens : str ∈ evens := by
        simp [List.mem_filter, isEven]
        exact ⟨hstr, str_even⟩
      have evens_nonempty : evens ≠ [] := List.ne_nil_of_mem str_in_evens
      cases' evens with first rest
      · contradiction
      · simp [List.foldl] at h
        induction rest generalizing head first with
        | nil => 
          simp at h
          rw [h]
          cases str_in_evens with
          | head => right; exact ⟨rfl, le_refl _⟩
          | tail h_tail => contradiction
        | cons a as ih =>
          simp [List.foldl] at h
          cases str_in_evens with
          | head => right; exact ⟨rfl, le_refl _⟩
          | tail h_tail => 
            cases h_tail with
            | head => right; exact ⟨rfl, le_refl _⟩
            | tail h_tail2 => left; linarith
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
    · split with h'
      · simp [findMinEven] at h'
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
      · have ⟨head_in_lst, head_even, head_properties⟩ := findMinEven_properties lst h' h'
        constructor
        · exact head_even
        constructor
        · exact head_properties
        · rfl
    · exact all_odd_case lst h