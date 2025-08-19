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
def findMinEven (lst: List String) : Option String :=
  let evens := lst.filter (fun s => Even s.length)
  match evens with
  | [] => none
  | _ => evens.minimum?

-- LLM HELPER
def hasEvenLength (lst: List String) : Bool :=
  lst.any (fun s => Even s.length)

def implementation (lst: List String) : List String :=
  if hasEvenLength lst then
    match findMinEven lst with
    | none => []
    | some head => head :: implementation (lst.erase head)
  else
    []

-- LLM HELPER
lemma all_odd_case (lst: List String) 
  (h: ¬hasEvenLength lst) : 
  ∀ str ∈ lst, Odd str.length := by
  intro str hstr
  by_contra hodd
  have heven : Even str.length := by
    cases' Nat.even_or_odd str.length with he ho
    · exact he
    · contradiction
  have : hasEvenLength lst := by
    simp [hasEvenLength]
    use str
    exact ⟨hstr, heven⟩
  contradiction

-- LLM HELPER
lemma findMinEven_properties (lst: List String) (head: String)
  (h: findMinEven lst = some head) :
  head ∈ lst ∧ Even head.length ∧
  ∀ str ∈ lst, Odd str.length ∨ str.length > head.length ∨ str.length = head.length ∧ str ≥ head := by
  constructor
  · simp [findMinEven] at h
    have evens_nonempty : (lst.filter (fun s => Even s.length)).length > 0 := by
      simp at h
      cases' lst.filter (fun s => Even s.length) with
      | nil => simp at h
      | cons hd tl => simp
    have head_in_evens : head ∈ lst.filter (fun s => Even s.length) := by
      simp [findMinEven] at h
      rw [List.minimum?_eq_some_iff] at h
      exact h.1
    simp [List.mem_filter] at head_in_evens
    exact head_in_evens.1
  constructor
  · simp [findMinEven] at h
    have head_in_evens : head ∈ lst.filter (fun s => Even s.length) := by
      rw [List.minimum?_eq_some_iff] at h
      exact h.1
    simp [List.mem_filter] at head_in_evens
    exact head_in_evens.2
  · intro str hstr
    simp [findMinEven] at h
    rw [List.minimum?_eq_some_iff] at h
    cases' Nat.even_or_odd str.length with heven hodd
    · right
      right
      have str_in_evens : str ∈ lst.filter (fun s => Even s.length) := by
        simp [List.mem_filter]
        exact ⟨hstr, heven⟩
      have : head ≤ str := h.2 str str_in_evens
      cases' Nat.lt_or_eq_of_le this with hlt heq
      · left
        exact hlt
      · right
        exact ⟨heq.symm, this⟩
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
        have : lst.filter (fun s => Even s.length) = [] := by
          simp [hasEvenLength, List.any_eq_true] at h
          by_contra hne
          have : ∃ s ∈ lst, Even s.length := by
            have nonempty : (lst.filter (fun s => Even s.length)).length > 0 := by
              rw [List.length_pos_iff_ne_nil]
              exact hne
            have ⟨s, hs⟩ := List.exists_mem_of_length_pos nonempty
            simp [List.mem_filter] at hs
            exact ⟨s, hs⟩
          simp [hasEvenLength, List.any_eq_true] at h
          exact h this
        have : ∀ str ∈ lst, Odd str.length := by
          intro str hstr
          by_contra hodd
          have heven : Even str.length := by
            cases' Nat.even_or_odd str.length with he ho
            · exact he
            · contradiction
          have str_in_filter : str ∈ lst.filter (fun s => Even s.length) := by
            simp [List.mem_filter]
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