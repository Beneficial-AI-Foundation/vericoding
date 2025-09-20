-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def is_prime (n : Nat) : Bool :=
sorry

def get_factors (n : Nat) : List Nat :=
sorry

def prime_factors (n : Nat) : String :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem prime_factors_valid_format (n : Nat) (h : n ≥ 2) :
  let result := prime_factors n
  ∀ part : String,
  part ∈ (String.split (prime_factors n) (· == ')')).filter (λ x => x ≠ "") →
  (∃ base power : Nat,
   ((String.contains part '*') →
    part = s!"{base}**{power}" ∧
    is_prime base ∧
    power > 1) ∧
   (¬String.contains part '*' →
    part.toNat?.isSome ∧
    is_prime part.toNat!)) :=
sorry

theorem prime_factors_preserves_value (n : Nat) (h : n ≥ 2) :
  let result := prime_factors n
  let parts := (String.split result (· == ')')).filter (λ x => x ≠ "")
  let reconstructed := parts.foldl
    (λ acc part =>
      if String.contains part '*'
      then
        let nums := String.split part (· == '*')
        let base := (nums.get! 0).trim.toNat!
        let power := (nums.get! 2).trim.toNat!
        acc * (base ^ power)
      else acc * part.trim.toNat!)
    1
  reconstructed = n :=
sorry

theorem prime_number_input (p : Nat) (h₁ : p ≥ 2) (h₂ : is_prime p) :
  prime_factors p = s!"({p})" :=
sorry

theorem powers_of_two (n : Nat) (h : n ≥ 1) :
  prime_factors (2^n) = s!"(2**{n})" :=
sorry
-- </vc-theorems>