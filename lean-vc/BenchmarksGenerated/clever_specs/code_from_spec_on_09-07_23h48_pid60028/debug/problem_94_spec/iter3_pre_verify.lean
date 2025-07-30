def problem_spec
-- function signature
(implementation: List Nat → Nat)
-- inputs
(lst: List Nat) :=
-- spec
let spec (result : Nat) :=
  lst.any (fun num => Nat.prime num) →
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
  have h_digits : (Nat.digits 10 p).length > 0 := Nat.digits_ne_nil_of_pos h_pos
  have h_sum : (Nat.digits 10 p).sum ≥ 1 := by
    apply Nat.succ_le_iff.mpr
    rw [Nat.sum_pos_iff_exists_pos]
    use (Nat.digits 10 p).head!
    constructor
    · apply List.head!_mem
      exact List.ne_nil_of_length_pos h_digits
    · have h_digit : (Nat.digits 10 p).head! < 10 := by
        apply Nat.digits_lt_base
        exact List.head!_mem (List.ne_nil_of_length_pos h_digits)
      have h_nonzero : (Nat.digits 10 p).head! ≠ 0 := by
        intro h_zero
        have h_last := Nat.digits_last 10 p h_pos
        rw [h_zero] at h_last
        exact Nat.not_lt_zero 0 h_last
      exact Nat.pos_of_ne_zero h_nonzero
  exact h_sum

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