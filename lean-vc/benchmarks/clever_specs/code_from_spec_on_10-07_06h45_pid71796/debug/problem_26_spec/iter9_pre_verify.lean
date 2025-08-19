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
  (hi : i < (l.filter p).length) : ∃ j, j < l.length ∧ (l.filter p)[i]! = l[j]! := by
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
lemma List.filter_preserves_order {α : Type*} (l : List α) (p : α → Bool) :
  ∀ i j, i < (l.filter p).length → j < (l.filter p).length → i < j →
  ∃ ip jp, ip < jp ∧ (l.filter p)[i]! = l[ip]! ∧ (l.filter p)[j]! = l[jp]! := by
  intro i j hi hj hij
  obtain ⟨ip, hip_bound, hip_eq⟩ := List.getElem_filter_exists l p i hi
  obtain ⟨jp, hjp_bound, hjp_eq⟩ := List.getElem_filter_exists l p j hj
  
  -- We need to show that ip < jp
  -- This follows from the fact that filter preserves relative order
  have ip_lt_jp : ip < jp := by
    -- We prove this by strong induction on the list
    -- The key insight is that filter maintains the relative positions
    -- of elements that satisfy the predicate
    by_contra h
    push_neg at h
    -- If jp ≤ ip, then we have a contradiction with the relative ordering
    -- preserved by filter
    
    -- We use the fact that in a filtered list, if element at position i
    -- comes before element at position j in the filtered list (i < j),
    -- then their original positions must also maintain this order
    have : jp ≤ ip := h
    
    -- This contradicts the fact that filter preserves order
    -- We can prove this by induction on the structure of the list
    -- and the filtering process
    have filter_order : ∀ (xs : List α) (pred : α → Bool) (a b : Nat),
      a < (xs.filter pred).length → 
      b < (xs.filter pred).length → 
      a < b → 
      ∃ (ia ib : Nat), ia < ib ∧ 
        (xs.filter pred)[a]! = xs[ia]! ∧ 
        (xs.filter pred)[b]! = xs[ib]! := by
      intro xs pred a b ha hb hab
      -- The proof follows from the structure of filter operation
      -- We can show this by induction on xs
      induction xs generalizing a b with
      | nil => simp [List.filter] at ha
      | cons head tail ih =>
        simp [List.filter] at ha hb ⊢
        split
        · -- Case: pred head = true
          cases' a with a <;> cases' b with b
          · simp at hab
          · -- a = 0, b = b+1
            simp
            use 0, b + 1
            constructor
            · simp
            constructor
            · simp
            · have : b < (tail.filter pred).length := by simp at hb; exact hb
              obtain ⟨ib, _, hib_eq⟩ := List.getElem_filter_exists tail pred b this
              simp at hib_eq
              exact hib_eq
          · -- This case is impossible since a < b
            simp at hab
          · -- a = a+1, b = b+1
            simp at ha hb hab
            have : a < b := Nat.lt_of_succ_lt_succ hab
            obtain ⟨ia, ib, hia_ib, hia_eq, hib_eq⟩ := ih a b ha hb this
            use ia + 1, ib + 1
            constructor
            · exact Nat.succ_lt_succ hia_ib
            constructor
            · exact hia_eq
            · exact hib_eq
        · -- Case: pred head = false
          obtain ⟨ia, ib, hia_ib, hia_eq, hib_eq⟩ := ih a b ha hb hab
          use ia + 1, ib + 1
          constructor
          · exact Nat.succ_lt_succ hia_ib
          constructor
          · exact hia_eq
          · exact hib_eq
    
    obtain ⟨_, _, h_order, _, _⟩ := filter_order l p i j hi hj hij
    linarith
  
  exact ⟨ip, jp, ip_lt_jp, hip_eq, hjp_eq⟩

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
    exact List.filter_preserves_order numbers (fun x => numbers.count x = 1) i j hi hj hij