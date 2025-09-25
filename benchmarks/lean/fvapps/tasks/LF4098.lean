-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def body_count (s : String) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem valid_code_returns_true {code : String}
  (h : ∃ (a₁ a₂ a₃ a₄ a₅ : Char) (n₁ n₂ n₃ n₄ n₅ : Nat) (last_letter : Char)
        (last_num dec₁ dec₂ : Nat),
    'A' ≤ a₁ ∧ a₁ ≤ 'Z' ∧
    'A' ≤ a₂ ∧ a₂ ≤ 'Z' ∧
    'A' ≤ a₃ ∧ a₃ ≤ 'Z' ∧
    'A' ≤ a₄ ∧ a₄ ≤ 'Z' ∧
    'A' ≤ a₅ ∧ a₅ ≤ 'Z' ∧
    'A' ≤ last_letter ∧ last_letter ≤ 'Z' ∧
    n₁ ≤ 9 ∧ n₂ ≤ 9 ∧ n₃ ≤ 9 ∧ n₄ ≤ 9 ∧ n₅ ≤ 9 ∧
    last_num ≤ 9 ∧
    dec₁ ≤ 9 ∧ dec₂ ≤ 9 ∧
    code = String.mk [a₁, Char.ofNat (n₁ + 48),
                     a₂, Char.ofNat (n₂ + 48),
                     a₃, Char.ofNat (n₃ + 48),
                     a₄, Char.ofNat (n₄ + 48),
                     a₅, Char.ofNat (n₅ + 48),
                     '.', '-', last_letter, '%',
                     Char.ofNat (last_num + 48), '.',
                     Char.ofNat (dec₁ + 48), Char.ofNat (dec₂ + 48), '.']) :
  body_count code = true :=
sorry

theorem invalid_code_returns_false {s : String}
  (h : ¬∃ (a₁ a₂ a₃ a₄ a₅ : Char) (n₁ n₂ n₃ n₄ n₅ : Nat) (last_letter : Char)
        (last_num dec₁ dec₂ : Nat),
    'A' ≤ a₁ ∧ a₁ ≤ 'Z' ∧
    'A' ≤ a₂ ∧ a₂ ≤ 'Z' ∧
    'A' ≤ a₃ ∧ a₃ ≤ 'Z' ∧
    'A' ≤ a₄ ∧ a₄ ≤ 'Z' ∧
    'A' ≤ a₅ ∧ a₅ ≤ 'Z' ∧
    'A' ≤ last_letter ∧ last_letter ≤ 'Z' ∧
    n₁ ≤ 9 ∧ n₂ ≤ 9 ∧ n₃ ≤ 9 ∧ n₄ ≤ 9 ∧ n₅ ≤ 9 ∧
    last_num ≤ 9 ∧
    dec₁ ≤ 9 ∧ dec₂ ≤ 9 ∧
    s = String.mk [a₁, Char.ofNat (n₁ + 48),
                  a₂, Char.ofNat (n₂ + 48),
                  a₃, Char.ofNat (n₃ + 48),
                  a₄, Char.ofNat (n₄ + 48),
                  a₅, Char.ofNat (n₅ + 48),
                  '.', '-', last_letter, '%',
                  Char.ofNat (last_num + 48), '.',
                  Char.ofNat (dec₁ + 48), Char.ofNat (dec₂ + 48), '.']) :
  body_count s = false :=
sorry
-- </vc-theorems>