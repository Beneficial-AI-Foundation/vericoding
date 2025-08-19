def problem_spec
-- function signature
(implementation: List Int → List Int)
-- inputs
(numbers: List Int) :=
-- spec
let spec (result: List Int) :=
(∀ i: Int, i ∈ result → numbers.count i = 1) ∧
(∀ i: Int, i ∈ numbers → numbers.count i = 1 → i ∈ result) ∧
(∀ i j : Nat, i < result.length → j < result.length → i < j →
∃ ip jp : Nat, ip < jp ∧ result[i]! = numbers[ip]! ∧ result[j]! = numbers[jp]!)
-- program termination
∃ result, implementation numbers = result ∧
spec result

-- LLM HELPER
def filterUnique (numbers: List Int) : List Int :=
  numbers.filter (fun x => numbers.count x = 1)

def implementation (numbers: List Int) : List Int := 
  filterUnique numbers

-- LLM HELPER
lemma filterUnique_correct (numbers: List Int) :
  ∀ x, x ∈ filterUnique numbers ↔ (x ∈ numbers ∧ numbers.count x = 1) := by
  intro x
  simp [filterUnique, List.mem_filter]

-- LLM HELPER
lemma List.getElem_filter_exists {α : Type*} (l : List α) (p : α → Bool) (i : Nat) 
  (hi : i < (l.filter p).length) : ∃ j, j < l.length ∧ (l.filter p).get ⟨i, hi⟩ = l.get ⟨j, by assumption⟩ := by
  induction l generalizing i with
  | nil => 
    simp [List.filter] at hi
  | cons head tail ih =>
    simp [List.filter] at hi ⊢
    split at hi
    · -- p head = true
      cases' i with i
      · simp
        use 0
        constructor
        · exact Nat.zero_lt_succ _
        · rfl
      · simp at hi
        obtain ⟨j, hj_bound, hj_eq⟩ := ih i hi
        use j + 1
        constructor
        · exact Nat.succ_lt_succ hj_bound
        · exact hj_eq
    · -- p head = false
      obtain ⟨j, hj_bound, hj_eq⟩ := ih i hi
      use j + 1
      constructor
      · exact Nat.succ_lt_succ hj_bound
      · exact hj_eq

-- LLM HELPER
lemma List.filter_index_monotone {α : Type*} (l : List α) (p : α → Bool) :
  ∀ i j, i < (l.filter p).length → j < (l.filter p).length → i < j →
  ∃ ip jp, ip < jp ∧ (l.filter p).get ⟨i, by assumption⟩ = l.get ⟨ip, by assumption⟩ ∧ (l.filter p).get ⟨j, by assumption⟩ = l.get ⟨jp, by assumption⟩ := by
  intro i j hi hj hij
  obtain ⟨ip, hip_bound, hip_eq⟩ := List.getElem_filter_exists l p i hi
  obtain ⟨jp, hjp_bound, hjp_eq⟩ := List.getElem_filter_exists l p j hj
  
  -- The key insight: filter maintains relative order
  have ip_lt_jp : ip < jp := by
    -- We need to prove that indices in the original list maintain order
    -- This follows from the fact that filter preserves the relative order
    -- of elements that satisfy the predicate
    induction l generalizing i j ip jp with
    | nil => simp [List.filter] at hi
    | cons head tail ih =>
      simp [List.filter] at *
      split
      · -- case: p head = true
        cases' i with i <;> cases' j with j
        · simp at hij
        · simp at hip_eq hjp_eq
          cases' ip with ip <;> cases' jp with jp
          · simp at hip_eq hjp_eq
            subst hip_eq hjp_eq
            simp
          · simp at hip_eq hjp_eq
            subst hip_eq
            simp
        · contradiction
        · simp at hip_eq hjp_eq hi hj hij
          cases' ip with ip <;> cases' jp with jp
          · simp at hip_eq hjp_eq
            subst hip_eq
            cases' jp with jp
            · simp at hjp_eq
              subst hjp_eq
              have : i < j := Nat.lt_of_succ_lt_succ hij
              have := ih i j hi hj this 0 0 rfl rfl
              simp at this
            · simp at hjp_eq
              simp
          · simp at hip_eq hjp_eq
            cases' jp with jp
            · simp at hjp_eq
              subst hjp_eq
              simp
            · simp at hip_eq hjp_eq
              have : i < j := Nat.lt_of_succ_lt_succ hij
              have := ih i j hi hj this ip jp hip_eq hjp_eq
              exact Nat.succ_lt_succ this
      · -- case: p head = false
        have := ih i j hi hj hij ip jp hip_eq hjp_eq
        exact Nat.succ_lt_succ this
  
  exact ⟨ip, jp, ip_lt_jp, hip_eq, hjp_eq⟩

-- LLM HELPER
lemma List.get_eq_getElem (l : List α) (i : Nat) (h : i < l.length) : 
  l.get ⟨i, h⟩ = l[i]! := by
  simp [List.getElem_eq_getElem!]

theorem correctness
(numbers: List Int)
: problem_spec implementation numbers := by
  simp [problem_spec, implementation]
  use filterUnique numbers
  constructor
  · rfl
  constructor
  · -- First condition: ∀ i: Int, i ∈ result → numbers.count i = 1
    intro i hi
    rw [filterUnique_correct] at hi
    exact hi.2
  constructor
  · -- Second condition: ∀ i: Int, i ∈ numbers → numbers.count i = 1 → i ∈ result
    intro i hi hcount
    rw [filterUnique_correct]
    exact ⟨hi, hcount⟩
  · -- Third condition: order preservation
    intro i j hi hj hij
    have mono := List.filter_index_monotone numbers (fun x => numbers.count x = 1) i j hi hj hij
    obtain ⟨ip, jp, hip_jp, hip_eq, hjp_eq⟩ := mono
    use ip, jp
    constructor
    · exact hip_jp
    constructor
    · rw [List.get_eq_getElem] at hip_eq
      exact hip_eq
    · rw [List.get_eq_getElem] at hjp_eq
      exact hjp_eq