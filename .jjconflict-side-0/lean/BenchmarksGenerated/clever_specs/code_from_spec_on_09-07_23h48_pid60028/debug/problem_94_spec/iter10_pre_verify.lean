def problem_spec
-- function signature
(implementation: List Nat → Nat)
-- inputs
(lst: List Nat) :=
-- spec
let spec (result : Nat) :=
  lst.any (fun num => Nat.prime num) = true →
    result > 0 ∧ ∃ i, i < lst.length ∧ Nat.prime (lst[i]!) ∧
    (∀ j, j < lst.length ∧ Nat.prime (lst[j]!) → lst[i]! ≤ lst[j]!) ∧
    result = (Nat.digits 10 (lst[i]!)).sum
-- program termination
∃ result,
  implementation lst = result ∧
  spec result

-- LLM HELPER
def findMinPrime (lst: List Nat) : Option Nat :=
  let primes := lst.filter Nat.prime
  if primes.isEmpty then none
  else primes.minimum?

-- LLM HELPER
def digitSum (n: Nat) : Nat :=
  (Nat.digits 10 n).sum

def implementation (lst: List Nat) : Nat :=
  match findMinPrime lst with
  | none => 0
  | some minPrime => digitSum minPrime

-- LLM HELPER
lemma digitSum_pos_of_prime (p: Nat) (hp: Nat.prime p) : digitSum p > 0 := by
  unfold digitSum
  have h_pos : p > 0 := Nat.Prime.pos hp
  have h_digits_ne_nil : (Nat.digits 10 p) ≠ [] := by
    rw [Nat.digits_ne_nil_iff_ne_zero]
    exact Nat.Prime.ne_zero hp
  have h_sum_pos : (Nat.digits 10 p).sum > 0 := by
    rw [List.sum_pos_iff_exists_pos]
    use (Nat.digits 10 p).head!
    constructor
    · apply List.head!_mem
      exact h_digits_ne_nil
    · have h_digit_nonzero : (Nat.digits 10 p).head! ≠ 0 := by
        intro h_zero
        have h_last := Nat.digits_last 10 p h_pos
        rw [List.head!_eq_head] at h_zero
        rw [Nat.digits_last_eq_last_digit] at h_last
        have h_last_nonzero : (Nat.digits 10 p).getLast h_digits_ne_nil ≠ 0 := by
          exact Nat.pos_of_ne_zero (Nat.Prime.ne_zero hp)
        have h_first_eq_last : (Nat.digits 10 p).head! = (Nat.digits 10 p).getLast h_digits_ne_nil := by
          cases' h_len : (Nat.digits 10 p).length with n
          · exact absurd h_len (List.length_pos_of_ne_nil h_digits_ne_nil)
          · cases n with
            | zero => simp [List.head!, List.getLast]
            | succ m => simp [List.head!, List.getLast]
        rw [h_first_eq_last] at h_zero
        exact h_last_nonzero h_zero
      exact Nat.pos_of_ne_zero h_digit_nonzero
  exact h_sum_pos

-- LLM HELPER
lemma findMinPrime_correct (lst: List Nat) :
  match findMinPrime lst with
  | none => ¬lst.any (fun num => Nat.prime num)
  | some p => Nat.prime p ∧ p ∈ lst ∧ (∀ q ∈ lst, Nat.prime q → p ≤ q) := by
  unfold findMinPrime
  simp only [List.isEmpty_iff_eq_nil]
  split_ifs with h
  · simp
    intro h_any
    rw [List.any_eq_true] at h_any
    obtain ⟨x, hx_mem, hx_prime⟩ := h_any
    have h_filter : x ∈ lst.filter Nat.prime := List.mem_filter.mpr ⟨hx_mem, hx_prime⟩
    rw [h] at h_filter
    exact List.not_mem_nil x h_filter
  · simp
    have h_nonempty : (lst.filter Nat.prime) ≠ [] := h
    have h_min := List.minimum?_mem h_nonempty
    obtain ⟨h_mem_filter, h_is_min⟩ := h_min
    have h_prime := List.mem_filter.mp h_mem_filter |>.2
    have h_mem := List.mem_filter.mp h_mem_filter |>.1
    exact ⟨h_prime, h_mem, fun q hq_mem hq_prime => h_is_min q (List.mem_filter.mpr ⟨hq_mem, hq_prime⟩)⟩

-- LLM HELPER
lemma mem_implies_get_at_some_index (lst: List Nat) (x: Nat) (hx: x ∈ lst) :
  ∃ i, i < lst.length ∧ lst[i]! = x := by
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hx
  use i
  constructor
  · exact i.2
  · rw [List.get!_eq_get]
    exact hi

theorem correctness
(lst: List Nat)
: problem_spec implementation lst := by
  unfold problem_spec implementation
  use implementation lst
  constructor
  · rfl
  · intro h_any_prime
    unfold implementation
    have h_find := findMinPrime_correct lst
    cases h_find_eq : findMinPrime lst with
    | none => 
      have h_no_prime := h_find
      rw [h_find_eq] at h_no_prime
      exact absurd h_any_prime h_no_prime
    | some minPrime =>
      have h_min_prime := h_find
      rw [h_find_eq] at h_min_prime
      obtain ⟨h_prime, h_mem, h_min⟩ := h_min_prime
      constructor
      · exact digitSum_pos_of_prime minPrime h_prime
      · obtain ⟨i, hi_bound, hi_eq⟩ := mem_implies_get_at_some_index lst minPrime h_mem
        use i
        constructor
        · exact hi_bound
        · constructor
          · rw [hi_eq]; exact h_prime
          · constructor
            · intro j hj_bound hj_prime
              rw [hi_eq]
              have h_mem_j : lst[j]! ∈ lst := by
                rw [List.get!_eq_get]
                exact List.get_mem lst j ⟨hj_bound⟩
              exact h_min (lst[j]!) h_mem_j hj_prime
            · rw [hi_eq]; rfl