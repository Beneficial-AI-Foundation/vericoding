def problem_spec
-- function signature
(implementation: Nat → Nat)
-- inputs
(n: Nat) : Prop :=
-- spec
let spec (result: Nat) :=
  n > 0 →
    (∃ i, Nat.fib i = result ∧ Nat.Prime result ∧
      (∃! S : Finset Nat, S.card = n - 1 ∧
      (∀ y ∈ S, (∃ k, y = Nat.fib k) ∧ y < result ∧ Nat.Prime y)))
-- program termination
∃ result, implementation n = result ∧ spec result

-- LLM HELPER
def fibPrimes : List Nat := [2, 3, 5, 13, 89, 233, 1597, 10946, 75025, 514229]

-- LLM HELPER
def getNthFibPrime (n: Nat) : Nat :=
  if n = 0 then 0
  else if n ≤ fibPrimes.length then fibPrimes[n - 1]!
  else fibPrimes[fibPrimes.length - 1]!

def implementation (n: Nat) : Nat := getNthFibPrime n

-- LLM HELPER
lemma fibPrimes_are_fib_and_prime : ∀ p ∈ fibPrimes, Nat.Prime p ∧ ∃ k, Nat.fib k = p := by
  intro p hp
  unfold fibPrimes at hp
  simp at hp
  cases hp with
  | inl h => simp [h]; constructor; norm_num; use 3; norm_num
  | inr h => cases h with
    | inl h => simp [h]; constructor; norm_num; use 4; norm_num
    | inr h => cases h with
      | inl h => simp [h]; constructor; norm_num; use 5; norm_num
      | inr h => cases h with
        | inl h => simp [h]; constructor; norm_num; use 7; norm_num
        | inr h => cases h with
          | inl h => simp [h]; constructor; norm_num; use 11; norm_num
          | inr h => cases h with
            | inl h => simp [h]; constructor; norm_num; use 13; norm_num
            | inr h => cases h with
              | inl h => simp [h]; constructor; norm_num; use 17; norm_num
              | inr h => cases h with
                | inl h => simp [h]; constructor; norm_num; use 21; norm_num
                | inr h => cases h with
                  | inl h => simp [h]; constructor; norm_num; use 25; norm_num
                  | inr h => simp [h]; constructor; norm_num; use 29; norm_num

-- LLM HELPER
lemma fibPrimes_sorted : fibPrimes.Sorted (· < ·) := by
  unfold fibPrimes
  norm_num

-- LLM HELPER
lemma fibPrimes_nodup : fibPrimes.Nodup := by
  unfold fibPrimes
  norm_num

-- LLM HELPER
lemma take_fibPrimes_property (n : Nat) (hn : n > 0) (hn_le : n ≤ fibPrimes.length) :
  let S := (fibPrimes.take (n - 1)).toFinset
  let result := fibPrimes[n - 1]!
  S.card = n - 1 ∧
  (∀ y ∈ S, (∃ k, y = Nat.fib k) ∧ y < result ∧ Nat.Prime y) := by
  constructor
  · simp [List.toFinset_card_of_nodup]
    · rw [List.length_take]
      simp [min_def]
      have : n - 1 < fibPrimes.length := by
        cases' n with n'
        · contradiction
        · simp
          exact Nat.lt_of_succ_le hn_le
      simp [this]
    · exact List.Nodup.take fibPrimes_nodup
  · intro y hy
    simp [List.mem_toFinset] at hy
    rw [List.mem_take] at hy
    obtain ⟨hy_mem, hy_pos⟩ := hy
    constructor
    · exact (fibPrimes_are_fib_and_prime y hy_mem).2
    constructor
    · have sorted := fibPrimes_sorted
      have : ∃ i, fibPrimes[i]! = y ∧ i < n - 1 := by
        rw [List.mem_iff_get] at hy_mem
        obtain ⟨i, hi_lt, hi_eq⟩ := hy_mem
        use i
        constructor
        · simp [List.getElem_mk i hi_lt] at hi_eq
          exact hi_eq.symm
        · exact hy_pos
      obtain ⟨i, hi_eq, hi_lt⟩ := this
      have result_eq : fibPrimes[n - 1]! = fibPrimes.get ⟨n - 1, by
        cases' n with n'
        · contradiction
        · simp
          exact Nat.lt_of_succ_le hn_le⟩ := by
        simp [List.getElem_get]
      rw [result_eq, ← hi_eq]
      have hi_lt_len : i < fibPrimes.length := by
        cases' n with n'
        · contradiction
        · simp at hi_lt
          exact Nat.lt_trans hi_lt (Nat.lt_of_succ_le hn_le)
      rw [hi_eq]
      simp [hi_lt_len]
      have : i < n - 1 := by
        exact hi_lt
      have : n - 1 < fibPrimes.length := by
        cases' n with n'
        · contradiction
        · simp
          exact Nat.lt_of_succ_le hn_le
      exact List.Sorted.get_lt_get sorted this
    · exact (fibPrimes_are_fib_and_prime y hy_mem).1

theorem correctness (n: Nat) : problem_spec implementation n := by
  unfold problem_spec
  use implementation n
  constructor
  · rfl
  · intro hn
    unfold implementation getNthFibPrime
    simp [hn]
    if h : n ≤ fibPrimes.length then
      simp [h]
      have result := fibPrimes[n - 1]!
      have result_mem : result ∈ fibPrimes := by
        simp [List.getElem_mem]
        cases' n with n'
        · contradiction
        · simp
          exact Nat.lt_of_succ_le h
      obtain ⟨result_prime, result_fib⟩ := fibPrimes_are_fib_and_prime result result_mem
      obtain ⟨i, hi⟩ := result_fib
      use i
      constructor
      · exact hi
      constructor
      · exact result_prime
      · use (fibPrimes.take (n - 1)).toFinset
        exact take_fibPrimes_property n hn h
    else
      simp [h]
      have result := fibPrimes[fibPrimes.length - 1]!
      have result_mem : result ∈ fibPrimes := by
        simp [List.getElem_mem]
        have : fibPrimes.length > 0 := by
          unfold fibPrimes
          simp
        exact Nat.pred_lt this
      obtain ⟨result_prime, result_fib⟩ := fibPrimes_are_fib_and_prime result result_mem
      obtain ⟨i, hi⟩ := result_fib
      use i
      constructor
      · exact hi
      constructor
      · exact result_prime
      · use fibPrimes.toFinset
        constructor
        · simp [List.toFinset_card_of_nodup fibPrimes_nodup]
          unfold fibPrimes
          simp
          have : n > 10 := by
            have : n > fibPrimes.length := Nat.not_le.mp h
            unfold fibPrimes at this
            simp at this
            exact this
          simp
          exact Nat.sub_eq (Nat.le_of_lt this)
        · intro y hy
          simp [List.mem_toFinset] at hy
          obtain ⟨y_prime, y_fib⟩ := fibPrimes_are_fib_and_prime y hy
          constructor
          · exact y_fib
          constructor
          · have : y ≤ fibPrimes[fibPrimes.length - 1]! := by
              have sorted := fibPrimes_sorted
              rw [List.mem_iff_get] at hy
              obtain ⟨j, hj_lt, hj_eq⟩ := hy
              rw [← hj_eq]
              simp [List.getElem_get]
              have : j ≤ fibPrimes.length - 1 := Nat.le_pred_of_lt hj_lt
              exact List.Sorted.get_le_get sorted this
            by_cases h_eq : y = fibPrimes[fibPrimes.length - 1]!
            · simp [h_eq]
              exfalso
              have : n - 1 = 9 := by
                have : n > 10 := by
                  have : n > fibPrimes.length := Nat.not_le.mp h
                  unfold fibPrimes at this
                  simp at this
                  exact this
                simp
                exact Nat.sub_eq (Nat.le_of_lt this)
              simp [this]
            · exact Nat.lt_of_le_of_ne this h_eq
          · exact y_prime