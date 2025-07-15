import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

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

def implementation (numbers: List Rat) : Rat :=
  if numbers.length = 0 then 0
  else
    let sorted := numbers.mergeSort (fun x y => decide (x ≤ y))
    let n := sorted.length
    if n % 2 = 1 then
      sorted[n / 2]?.getD 0
    else
      (sorted[n / 2 - 1]?.getD 0 + sorted[n / 2]?.getD 0) / 2

theorem correctness
(numbers: List Rat)
: problem_spec implementation numbers := by
  unfold problem_spec implementation
  cases' h_len : numbers.length with n
  · -- Case: numbers.length = 0
    use 0
    simp [h_len]
    intro h_pos
    exfalso
    omega
  · -- Case: numbers.length > 0
    have h_pos : 0 < numbers.length := by
      rw [h_len]
      simp
    
    let sorted := numbers.mergeSort (fun x y => decide (x ≤ y))
    let n := sorted.length
    have h_len' : n = numbers.length := by
      simp [sorted, List.length_mergeSort]
    
    cases' Nat.mod_two_eq_zero_or_one n with h_even h_odd
    · -- Even case
      let median := (sorted[n / 2 - 1]?.getD 0 + sorted[n / 2]?.getD 0) / 2
      use median
      constructor
      · simp [median, sorted, h_len']
        rw [h_len', h_even]
        simp
      · intro h_pos'
        constructor
        · intro h_count h_le1 h_le2
          constructor <;> assumption
        · constructor
          · intro h_odd_len
            rw [← h_len'] at h_odd_len
            rw [h_even] at h_odd_len
            simp at h_odd_len
          · intro h_even_len
            constructor
            · -- show max_more_eq.isSome
              simp [Option.isSome_iff_exists]
              use sorted[n / 2]?.getD 0
              simp [List.max?_eq_some_iff]
              constructor
              · -- show element is in filter
                simp [List.mem_filter]
                constructor
                · -- show element is in numbers
                  have h_valid : n / 2 < n := by
                    rw [h_len']
                    exact Nat.div_lt_self h_pos (by norm_num)
                  have : sorted[n / 2]?.getD 0 ∈ sorted := by
                    exact List.getD_mem (sorted[n / 2]?) sorted 0
                  rw [← List.Perm.mem_iff (List.perm_mergeSort numbers)]
                  exact this
                · -- show median ≤ element
                  sorry
              · -- show it's maximum
                sorry
            · constructor
              · -- show min_less_eq.isSome
                sorry
              · -- show 2 * median = max + min
                sorry
    · -- Odd case
      let median := sorted[n / 2]?.getD 0
      use median
      constructor
      · simp [median, sorted, h_len']
        rw [h_len', h_odd]
        simp
      · intro h_pos'
        constructor
        · intro h_count h_le1 h_le2
          constructor <;> assumption
        · constructor
          · intro h_odd_len
            have h_valid : n / 2 < n := by
              rw [h_len']
              exact Nat.div_lt_self h_pos (by norm_num)
            have : sorted[n / 2]?.getD 0 ∈ sorted := by
              exact List.getD_mem (sorted[n / 2]?) sorted 0
            rw [← List.Perm.mem_iff (List.perm_mergeSort numbers)]
            exact this
          · intro h_even_len
            rw [← h_len'] at h_even_len
            rw [h_odd] at h_even_len
            simp at h_even_len