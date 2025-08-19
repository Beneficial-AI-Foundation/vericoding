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

-- LLM HELPER
def preserveOrder (original: List Int) (filtered: List Int) : List Int :=
  original.filter (fun x => x ∈ filtered)

def implementation (numbers: List Int) : List Int := 
  preserveOrder numbers (filterUnique numbers)

-- LLM HELPER
lemma filterUnique_correct (numbers: List Int) :
  ∀ x, x ∈ filterUnique numbers ↔ (x ∈ numbers ∧ numbers.count x = 1) := by
  intro x
  simp [filterUnique, List.mem_filter]

-- LLM HELPER
lemma preserveOrder_subset (original filtered: List Int) :
  ∀ x, x ∈ preserveOrder original filtered → x ∈ original := by
  intro x h
  simp [preserveOrder, List.mem_filter] at h
  exact h.1

-- LLM HELPER
lemma preserveOrder_mem (original filtered: List Int) :
  ∀ x, x ∈ preserveOrder original filtered → x ∈ filtered := by
  intro x h
  simp [preserveOrder, List.mem_filter] at h
  exact h.2

-- LLM HELPER
lemma preserveOrder_order (original filtered: List Int) :
  ∀ i j, i < (preserveOrder original filtered).length → 
         j < (preserveOrder original filtered).length → 
         i < j →
  ∃ ip jp, ip < jp ∧ 
           (preserveOrder original filtered)[i]! = original[ip]! ∧ 
           (preserveOrder original filtered)[j]! = original[jp]! := by
  intro i j hi hj hij
  let result := preserveOrder original filtered
  have h1 : result[i]! ∈ original := by
    have : result[i]! ∈ result := List.getElem_mem result i hi
    exact preserveOrder_subset original filtered (result[i]!) this
  have h2 : result[j]! ∈ original := by
    have : result[j]! ∈ result := List.getElem_mem result j hj
    exact preserveOrder_subset original filtered (result[j]!) this
  
  -- Since result is a subsequence of original preserving order
  have : ∃ ip jp, ip < original.length ∧ jp < original.length ∧ 
                   ip < jp ∧ original[ip]! = result[i]! ∧ original[jp]! = result[j]! := by
    -- This follows from the definition of preserveOrder and filter preserving order
    simp [preserveOrder] at hi hj
    have result_def : result = original.filter (fun x => x ∈ filtered) := rfl
    rw [result_def] at hi hj hij
    -- Use the fact that filter preserves relative order
    have order_preserved : ∃ ip jp, ip < jp ∧ original[ip]! = result[i]! ∧ original[jp]! = result[j]! := by
      -- This is a property of filter preserving order
      apply List.filter_preserves_order
      exact hij
    exact order_preserved
  
  obtain ⟨ip, jp, _, _, hip_jp, hip_eq, hjp_eq⟩ := this
  exact ⟨ip, jp, hip_jp, hip_eq, hjp_eq⟩

-- LLM HELPER
lemma List.filter_preserves_order {α : Type*} (l : List α) (p : α → Bool) :
  ∀ i j, i < (l.filter p).length → j < (l.filter p).length → i < j →
  ∃ ip jp, ip < jp ∧ (l.filter p)[i]! = l[ip]! ∧ (l.filter p)[j]! = l[jp]! := by
  intro i j hi hj hij
  -- Use induction on the structure of filtered list
  have : ∃ indices : List Nat, indices.length = (l.filter p).length ∧ 
         (∀ k, k < indices.length → indices[k]! < l.length) ∧
         (∀ k, k < indices.length → l[indices[k]!]! = (l.filter p)[k]!) ∧
         (∀ k₁ k₂, k₁ < indices.length → k₂ < indices.length → k₁ < k₂ → indices[k₁]! < indices[k₂]!) := by
    apply List.filter_indices_exist
  obtain ⟨indices, hlen, hbound, heq, horder⟩ := this
  rw [← hlen] at hi hj
  exact ⟨indices[i]!, indices[j]!, horder i j hi hj hij, (heq i hi).symm, (heq j hj).symm⟩

-- LLM HELPER
lemma List.filter_indices_exist {α : Type*} (l : List α) (p : α → Bool) :
  ∃ indices : List Nat, indices.length = (l.filter p).length ∧ 
  (∀ k, k < indices.length → indices[k]! < l.length) ∧
  (∀ k, k < indices.length → l[indices[k]!]! = (l.filter p)[k]!) ∧
  (∀ k₁ k₂, k₁ < indices.length → k₂ < indices.length → k₁ < k₂ → indices[k₁]! < indices[k₂]!) := by
  induction l with
  | nil => 
    simp [List.filter]
    exact ⟨[], rfl, fun _ h => False.elim h, fun _ h => False.elim h, fun _ _ h => False.elim h⟩
  | cons head tail ih =>
    simp [List.filter]
    split
    · -- p head = true
      obtain ⟨tail_indices, hlen, hbound, heq, horder⟩ := ih
      let indices := 0 :: tail_indices.map (· + 1)
      use indices
      constructor
      · simp [indices]; rw [hlen]; rfl
      constructor
      · intro k hk
        simp [indices] at hk ⊢
        cases' k with k
        · simp
        · simp
          have : k < tail_indices.length := by
            simp at hk
            rw [hlen] at hk
            exact Nat.lt_of_succ_lt_succ hk
          exact Nat.succ_lt_succ (hbound k this)
      constructor
      · intro k hk
        simp [indices] at hk ⊢
        cases' k with k
        · simp
        · simp
          have : k < tail_indices.length := by
            simp at hk
            rw [hlen] at hk
            exact Nat.lt_of_succ_lt_succ hk
          rw [← heq k this]
          simp
      · intro k₁ k₂ hk₁ hk₂ hlt
        simp [indices] at hk₁ hk₂ ⊢
        cases' k₁ with k₁ <;> cases' k₂ with k₂
        · simp at hlt
        · simp
        · simp at hlt
        · simp
          have hk₁' : k₁ < tail_indices.length := by
            rw [hlen] at hk₁
            exact Nat.lt_of_succ_lt_succ hk₁
          have hk₂' : k₂ < tail_indices.length := by
            rw [hlen] at hk₂
            exact Nat.lt_of_succ_lt_succ hk₂
          have : k₁ < k₂ := Nat.lt_of_succ_lt_succ hlt
          exact Nat.succ_lt_succ (horder k₁ k₂ hk₁' hk₂' this)
    · -- p head = false
      obtain ⟨tail_indices, hlen, hbound, heq, horder⟩ := ih
      let indices := tail_indices.map (· + 1)
      use indices
      constructor
      · simp [indices, hlen]
      constructor
      · intro k hk
        simp [indices] at hk ⊢
        exact Nat.succ_lt_succ (hbound k (by rwa [hlen] at hk))
      constructor
      · intro k hk
        simp [indices] at hk ⊢
        rw [← heq k (by rwa [hlen] at hk)]
        simp
      · intro k₁ k₂ hk₁ hk₂ hlt
        simp [indices] at hk₁ hk₂ ⊢
        have hk₁' : k₁ < tail_indices.length := by rwa [hlen] at hk₁
        have hk₂' : k₂ < tail_indices.length := by rwa [hlen] at hk₂
        exact Nat.succ_lt_succ (horder k₁ k₂ hk₁' hk₂' hlt)

theorem correctness
(numbers: List Int)
: problem_spec implementation numbers
:= by
  simp [problem_spec, implementation]
  use preserveOrder numbers (filterUnique numbers)
  constructor
  · rfl
  constructor
  · -- First condition: ∀ i: Int, i ∈ result → numbers.count i = 1
    intro i hi
    have h1 : i ∈ filterUnique numbers := preserveOrder_mem numbers (filterUnique numbers) i hi
    rw [filterUnique_correct] at h1
    exact h1.2
  constructor
  · -- Second condition: ∀ i: Int, i ∈ numbers → numbers.count i = 1 → i ∈ result
    intro i hi hcount
    simp [preserveOrder, List.mem_filter]
    constructor
    · exact hi
    · rw [filterUnique_correct]
      exact ⟨hi, hcount⟩
  · -- Third condition: order preservation
    intro i j hi hj hij
    exact preserveOrder_order numbers (filterUnique numbers) i j hi hj hij