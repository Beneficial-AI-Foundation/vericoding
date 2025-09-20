-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def insert_dash (n : Nat) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem insert_dash_outputs_string : ∀ n : Nat,
  ∃ s : String, insert_dash n = s :=
sorry

theorem insert_dash_valid_chars : ∀ n : Nat,
  ∀ c ∈ (insert_dash n).data, c = '-' ∨ ('0'.toNat ≤ c.toNat ∧ c.toNat ≤ '9'.toNat) :=
sorry 

theorem insert_dash_preserves_digits : ∀ n : Nat,
  ((insert_dash n).data.filter (λ c => '0'.toNat ≤ c.toNat ∧ c.toNat ≤ '9'.toNat)).length = (toString n).length :=
sorry

theorem insert_dash_between_odd : ∀ n : Nat,
  let parts := (insert_dash n).split (· = '-')
  ∀ i, i + 1 < parts.length →
    let last_digit := parts[i]!.data[parts[i]!.length - 1]!
    let first_digit := parts[i+1]!.data[0]!
    (last_digit.toNat - '0'.toNat) % 2 = 1 ∧ 
    (first_digit.toNat - '0'.toNat) % 2 = 1 :=
sorry

theorem insert_dash_reversible : ∀ n : Nat,
  (String.toNat! ((insert_dash n).replace "-" "")) = n :=
sorry
-- </vc-theorems>