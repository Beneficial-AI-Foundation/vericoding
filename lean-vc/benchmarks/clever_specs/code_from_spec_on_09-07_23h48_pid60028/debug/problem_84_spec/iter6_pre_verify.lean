def problem_spec
-- function signature
(implementation: Nat → String)
-- inputs
(n: Nat) :=
-- spec
let spec (result : String) :=
  0 < n →
  result.all (fun c => c = '0' ∨ c = '1') →
  Nat.ofDigits 2 (result.data.map (fun c => if c = '0' then 0 else 1)).reverse = (Nat.digits 10 n).sum
-- program termination
∃ result,
  implementation n = result ∧
  spec result

-- LLM HELPER
def digitSum (n : Nat) : Nat :=
  if n = 0 then 0 else
  let rec aux (m : Nat) : Nat :=
    if m = 0 then 0
    else (m % 10) + aux (m / 10)
  aux n

-- LLM HELPER
def natToBinary (n : Nat) : String :=
  if n = 0 then "0"
  else
    let rec aux (m : Nat) : String :=
      if m = 0 then ""
      else aux (m / 2) ++ (if m % 2 = 0 then "0" else "1")
    aux n

def implementation (n: Nat) : String := 
  natToBinary (digitSum n)

-- LLM HELPER
lemma digitSum_eq_sum_digits (n : Nat) : digitSum n = (Nat.digits 10 n).sum := by
  simp [digitSum]
  if h : n = 0 then
    simp [h, Nat.digits]
  else
    simp [h]
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      simp [digitSum.aux]
      if h : n = 0 then
        simp [h, Nat.digits]
      else
        simp [h]
        rw [Nat.digits_def]
        simp [Nat.sum_cons]
        rw [← ih (n / 10)]
        · simp [digitSum.aux]
        · exact Nat.div_lt_self (Nat.pos_of_ne_zero h) (by norm_num)

-- LLM HELPER
lemma natToBinary_all_binary (n : Nat) : (natToBinary n).all (fun c => c = '0' ∨ c = '1') := by
  simp [natToBinary]
  if h : n = 0 then
    simp [h, String.all]
  else
    simp [h]
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      simp [natToBinary.aux]
      if h : n = 0 then
        simp [h, String.all]
      else
        simp [h, String.all_append]
        constructor
        · exact ih (n / 2) (Nat.div_lt_self (Nat.pos_of_ne_zero h) (by norm_num))
        · simp [String.all]

-- LLM HELPER
lemma natToBinary_correct (n : Nat) : 
  Nat.ofDigits 2 ((natToBinary n).data.map (fun c => if c = '0' then 0 else 1)).reverse = n := by
  simp [natToBinary]
  if h : n = 0 then
    simp [h, Nat.ofDigits]
  else
    simp [h]
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      simp [natToBinary.aux]
      if h : n = 0 then
        simp [h, Nat.ofDigits]
      else
        simp [h]
        rw [String.data_append, List.map_append, List.reverse_append]
        simp [Nat.ofDigits_append]
        rw [ih (n / 2)]
        · simp [Nat.ofDigits]
          ring_nf
          rw [Nat.div_add_mod n 2]
        · exact Nat.div_lt_self (Nat.pos_of_ne_zero h) (by norm_num)

theorem correctness
(n: Nat)
: problem_spec implementation n := by
  simp [problem_spec, implementation]
  use natToBinary (digitSum n)
  constructor
  · rfl
  · intro h₁ h₂
    rw [digitSum_eq_sum_digits]
    exact natToBinary_correct (digitSum n)