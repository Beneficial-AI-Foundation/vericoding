def problem_spec
-- function signature
(implementation: List Rat → Rat)
-- inputs
(numbers: List Rat) :=
-- spec
let spec (result: Rat) :=
  0 < numbers.length →
  let less_eq := (numbers.filter (fun x => x ≤ result));
  let more_eq := (numbers.filter (fun x => result ≤ x));
  let max_more_eq := more_eq.max?;
  let min_less_eq := less_eq.min?;
  let less_eq_count := less_eq.length;
  let more_eq_count := more_eq.length;
  let eq_count := (numbers.filter (fun x => x = result)).length;
  (less_eq_count + more_eq_count - eq_count = numbers.length →
  numbers.length ≤ 2 * less_eq_count →
  numbers.length ≤ 2 * more_eq_count) ∧
  ((numbers.length % 2 = 1 →
    result ∈ numbers) ∧
    (numbers.length % 2 = 0 → max_more_eq.isSome ∧
    min_less_eq.isSome ∧
    2 * result = max_more_eq.get! + min_less_eq.get!));
-- program termination
∃ result, implementation numbers = result ∧
spec result

-- LLM HELPER
instance : LE Rat := ⟨Rat.le⟩

-- LLM HELPER
instance : Max Rat := ⟨fun x y => if x ≤ y then y else x⟩

-- LLM HELPER
instance : Min Rat := ⟨fun x y => if x ≤ y then x else y⟩

-- LLM HELPER
instance : OfNat Rat (n : Nat) := ⟨Rat.ofNat n⟩

-- LLM HELPER
instance : HAdd Rat Rat Rat := ⟨Rat.add⟩

-- LLM HELPER
instance : HMul Nat Rat Rat := ⟨fun n r => (Rat.ofNat n) * r⟩

-- LLM HELPER
instance : HDiv Rat Rat Rat := ⟨Rat.div⟩

-- LLM HELPER
instance : DecidableRel (· ≤ · : Rat → Rat → Prop) := Rat.decidable_le

-- LLM HELPER
instance : Inhabited Rat := ⟨0⟩

-- LLM HELPER
instance : DecidableEq Rat := Rat.decidableEq

-- LLM HELPER
instance : HMul Rat Rat Rat := ⟨Rat.mul⟩

def implementation (numbers: List Rat) : Rat :=
  if numbers.length = 0 then 0
  else
    let sorted := numbers.mergeSort (fun x y => x ≤ y)
    let n := sorted.length
    if n % 2 = 1 then
      sorted[n / 2]!
    else
      let mid1 := sorted[n / 2 - 1]!
      let mid2 := sorted[n / 2]!
      (mid1 + mid2) / 2

theorem correctness (numbers: List Rat) : problem_spec implementation numbers := by
  simp only [problem_spec, implementation]
  split_ifs with h_empty
  · use 0
    simp [h_empty]
  · let sorted := numbers.mergeSort (fun x y => x ≤ y)
    let n := sorted.length
    have h_n : n = numbers.length := by
      simp [sorted, n]
      rw [List.length_mergeSort]
    split_ifs with h_odd
    · use sorted[n / 2]!
      constructor
      · rfl
      · intro h_pos
        constructor
        · intro h_count h_less h_more
          simp [List.length_filter]
          omega
        · constructor
          · intro h_odd_case
            have h_perm : sorted ~ numbers := List.perm_mergeSort _ _
            have h_mem : sorted[n / 2]! ∈ sorted := by
              apply List.get!_mem
              rw [h_n]
              omega
            exact List.Perm.mem_iff h_perm |>.mp h_mem
          · intro h_even
            rw [h_n] at h_odd
            rw [h_odd] at h_even
            simp at h_even
    · use (sorted[n / 2 - 1]! + sorted[n / 2]!) / 2
      constructor
      · rfl
      · intro h_pos
        constructor
        · intro h_count h_less h_more
          simp [List.length_filter]
          omega
        · constructor
          · intro h_odd_case
            rw [h_n] at h_odd_case
            have h_not_odd : ¬(n % 2 = 1) := by
              rw [h_n]
              exact h_odd_case
            contradiction
          · intro h_even
            constructor
            · simp [List.max?_eq_none_iff]
              omega
            · constructor
              · simp [List.min?_eq_none_iff]
                omega
              · ring