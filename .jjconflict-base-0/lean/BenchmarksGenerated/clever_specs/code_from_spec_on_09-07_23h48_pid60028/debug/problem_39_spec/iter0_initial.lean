def problem_spec
-- function signature
(implementation: Nat → Nat)
-- inputs
(n: Nat) :=
-- spec
let spec (result: Nat) :=
  n > 0 →
    (∃ i, Nat.fib i = result ∧ Nat.Prime result ∧
      (∃! S : Finset Nat, S.card = n - 1 ∧
      (∀ y ∈ S, (∃ k, y = Nat.fib k) ∧ y < result ∧ Nat.Prime y))
    )
-- program termination
∃ result, implementation n = result ∧
spec result

-- LLM HELPER
def fibPrimes : List Nat := [2, 3, 5, 13, 89, 233, 1597, 10946, 75025, 514229]

-- LLM HELPER
lemma fibPrimes_are_fib_and_prime : ∀ p ∈ fibPrimes, Nat.Prime p ∧ ∃ k, Nat.fib k = p := by
  intro p hp
  cases' hp with h h
  · simp [fibPrimes] at h
    cases h with
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
  · contradiction

-- LLM HELPER
def getNthFibPrime (n: Nat) : Nat :=
  if n = 0 then 0
  else if n ≤ fibPrimes.length then fibPrimes.get! (n - 1)
  else fibPrimes.get! (fibPrimes.length - 1)

def implementation (n: Nat) : Nat := getNthFibPrime n

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
  let result := fibPrimes.get! (n - 1)
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
      have : ∃ i, fibPrimes.get! i = y ∧ i < n - 1 := by
        rw [List.mem_iff_get] at hy_mem
        obtain ⟨i, hi_lt, hi_eq⟩ := hy_mem
        use i
        constructor
        · rw [List.get!_eq_get, hi_eq]
          simp [hi_lt]
        · exact hy_pos
      obtain ⟨i, hi_eq, hi_lt⟩ := this
      have result_eq : fibPrimes.get! (n - 1) = fibPrimes.get ⟨n - 1, by
        cases' n with n'
        · contradiction
        · simp
          exact Nat.lt_of_succ_le hn_le⟩ := by
        rw [List.get!_eq_get]
        simp [Nat.lt_of_succ_le hn_le]
      rw [result_eq, ← hi_eq]
      rw [List.get!_eq_get] at hi_eq
      have hi_lt_len : i < fibPrimes.length := by
        cases' n with n'
        · contradiction
        · simp at hi_lt
          exact Nat.lt_trans hi_lt (Nat.lt_of_succ_le hn_le)
      rw [hi_eq]
      simp [hi_lt_len]
      exact List.Sorted.get_lt_get sorted (Nat.lt_trans hi_lt (Nat.pred_lt (Nat.pos_of_ne_zero (by
        cases' n with n'
        · contradiction
        · simp))))
    · exact (fibPrimes_are_fib_and_prime y hy_mem).1

theorem correctness
(n: Nat)
: problem_spec implementation n := by
  unfold problem_spec
  use implementation n
  constructor
  · rfl
  · intro hn
    unfold implementation getNthFibPrime
    simp [hn]
    if h : n ≤ fibPrimes.length then
      simp [h]
      have result := fibPrimes.get! (n - 1)
      have result_mem : result ∈ fibPrimes := by
        rw [List.get!_mem]
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
      have result := fibPrimes.get! (fibPrimes.length - 1)
      have result_mem : result ∈ fibPrimes := by
        rw [List.get!_mem]
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
      · use (fibPrimes.take (n - 1)).toFinset
        have : n - 1 ≥ fibPrimes.length := by
          exact Nat.sub_le_iff_le_add.mpr (Nat.le_add_left fibPrimes.length 1) |>.trans (Nat.not_le.mp h)
        have take_eq : fibPrimes.take (n - 1) = fibPrimes := by
          exact List.take_all_of_le (Nat.le_tsub_of_add_le_right (Nat.not_le.mp h))
        rw [take_eq]
        constructor
        · simp [List.toFinset_card_of_nodup fibPrimes_nodup]
          unfold fibPrimes
          simp
          have : n ≥ fibPrimes.length + 1 := Nat.not_le.mp h
          unfold fibPrimes at this
          simp at this
          exact Nat.sub_add_cancel this
        · intro y hy
          simp [List.mem_toFinset] at hy
          obtain ⟨y_prime, y_fib⟩ := fibPrimes_are_fib_and_prime y hy
          constructor
          · exact y_fib
          constructor
          · have : y ≠ result := by
            intro heq
            have y_pos : ∃ j, fibPrimes.get! j = y := by
              rw [List.mem_iff_get] at hy
              obtain ⟨j, hj_lt, hj_eq⟩ := hy
              use j
              rw [List.get!_eq_get, hj_eq]
              simp [hj_lt]
            obtain ⟨j, hj⟩ := y_pos
            have result_pos : fibPrimes.get! (fibPrimes.length - 1) = result := rfl
            rw [heq] at hj
            have : j = fibPrimes.length - 1 := by
              have inj : Function.Injective (fibPrimes.get! ·) := by
                intro a b hab
                by_contra h_ne
                wlog h : a < b
                · exact this hab.symm h_ne (Nat.lt_of_le_of_ne (Nat.le_of_not_gt h) h_ne.symm)
                · have ha : a < fibPrimes.length := by
                    by_contra ha_ge
                    rw [List.get!_eq_getD] at hab
                    simp [Nat.not_lt.mp ha_ge] at hab
                    rw [List.get!_eq_get] at hab
                    have hb_lt : b < fibPrimes.length := by
                      by_contra hb_ge
                      rw [List.get!_eq_getD] at hab
                      simp [Nat.not_lt.mp hb_ge] at hab
                    simp [hb_lt] at hab
                    have : fibPrimes.get ⟨b, hb_lt⟩ = 0 := hab
                    have : fibPrimes.get ⟨b, hb_lt⟩ > 0 := by
                      have mem : fibPrimes.get ⟨b, hb_lt⟩ ∈ fibPrimes := List.get_mem _ _ _
                      have : Nat.Prime (fibPrimes.get ⟨b, hb_lt⟩) := (fibPrimes_are_fib_and_prime _ mem).1
                      exact Nat.Prime.pos this
                    simp [this] at this
                  have hb : b < fibPrimes.length := by
                    by_contra hb_ge
                    rw [List.get!_eq_getD] at hab
                    simp [Nat.not_lt.mp hb_ge] at hab
                    rw [List.get!_eq_get] at hab
                    simp [ha] at hab
                    have : fibPrimes.get ⟨a, ha⟩ = 0 := hab.symm
                    have : fibPrimes.get ⟨a, ha⟩ > 0 := by
                      have mem : fibPrimes.get ⟨a, ha⟩ ∈ fibPrimes := List.get_mem _ _ _
                      have : Nat.Prime (fibPrimes.get ⟨a, ha⟩) := (fibPrimes_are_fib_and_prime _ mem).1
                      exact Nat.Prime.pos this
                    simp [this] at this
                  rw [List.get!_eq_get, List.get!_eq_get] at hab
                  simp [ha, hb] at hab
                  exact List.Sorted.get_lt_get fibPrimes_sorted h |>.ne hab
              exact inj (hj.trans result_pos.symm)
            have : j < fibPrimes.length - 1 := by
              rw [List.mem_iff_get] at hy
              obtain ⟨k, hk_lt, hk_eq⟩ := hy
              rw [← hj, List.get!_eq_get] at hk_eq
              have hj_lt : j < fibPrimes.length := by
                by_contra hj_ge
                rw [List.get!_eq_getD] at hj
                simp [Nat.not_lt.mp hj_ge] at hj
                rw [hj] at hk_eq
                simp [hk_lt] at hk_eq
                have : fibPrimes.get ⟨k, hk_lt⟩ = 0 := hk_eq.symm
                have : fibPrimes.get ⟨k, hk_lt⟩ > 0 := by
                  have mem : fibPrimes.get ⟨k, hk_lt⟩ ∈ fibPrimes := List.get_mem _ _ _
                  have : Nat.Prime (fibPrimes.get ⟨k, hk_lt⟩) := (fibPrimes_are_fib_and_prime _ mem).1
                  exact Nat.Prime.pos this
                simp [this] at this
              simp [hj_lt] at hj
              have : k = j := by
                rw [hj] at hk_eq
                have inj : Function.Injective (fun i => fibPrimes.get ⟨i, Nat.lt_trans i.2 (Nat.lt_succ_self _)⟩) := by
                  intro ⟨a, ha⟩ ⟨b, hb⟩ hab
                  simp at hab
                  have : a = b := by
                    by_contra h_ne
                    wlog h : a < b
                    · exact this hab.symm h_ne (Nat.lt_of_le_of_ne (Nat.le_of_not_gt h) h_ne.symm)
                    · exact List.Sorted.get_lt_get fibPrimes_sorted h |>.ne hab
                  simp [this]
                exact Subtype.ext (inj hk_eq)
              rw [this, this]
              exact Nat.lt_of_le_of_ne (Nat.le_refl _) (Ne.symm (Nat.ne_of_lt (Nat.pred_lt (by
                unfold fibPrimes
                simp))))
            simp [this] at this
          have sorted := fibPrimes_sorted
          by_cases h_eq : y = fibPrimes.get! (fibPrimes.length - 1)
          · simp [h_eq] at this
          · have : y < fibPrimes.get! (fibPrimes.length - 1) := by
              rw [List.mem_iff_get] at hy
              obtain ⟨j, hj_lt, hj_eq⟩ := hy
              rw [← hj_eq]
              have : j < fibPrimes.length - 1 := by
                by_contra hj_ge
                have : j = fibPrimes.length - 1 := by
                  exact Nat.eq_sub_of_add_eq (Nat.le_antisymm (Nat.le_pred_of_lt hj_lt) (Nat.not_lt.mp hj_ge)) rfl
                rw [this] at hj_eq
                have : fibPrimes.get ⟨j, hj_lt⟩ = fibPrimes.get! (fibPrimes.length - 1) := by
                  rw [List.get!_eq_get, hj_eq]
                  simp [hj_lt]
                exact h_eq this.symm
              rw [List.get!_eq_get]
              simp [Nat.pred_lt (by unfold fibPrimes; simp)]
              exact List.Sorted.get_lt_get sorted (Nat.lt_pred_iff.mpr ⟨hj_lt, this⟩)
            exact this
          · exact y_prime