-- <vc-preamble>
def IsLetter (c : Char) : Bool :=
(c ≥ 'a' ∧ c ≤ 'z') ∨ (c ≥ 'A' ∧ c ≤ 'Z')

def NoLetters (s : String) (n : Nat) : Prop :=
∀ i, 0 ≤ i ∧ i < n → ¬IsLetter (s.get ⟨i⟩)

def ToggleCase (c : Char) : Char :=
if c ≥ 'a' ∧ c ≤ 'z' then
Char.ofNat (Char.toNat c - Char.toNat 'a' + Char.toNat 'A')
else if c ≥ 'A' ∧ c ≤ 'Z' then
Char.ofNat (Char.toNat c - Char.toNat 'A' + Char.toNat 'a')
else c

def isReverse (s s_prime : String) : Prop :=
(s.length = s_prime.length) ∧
(∀ i, 0 ≤ i ∧ i < s.length/2 → s_prime.get ⟨s.length - i - 1⟩ = s.get ⟨i⟩)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Reverse (original : Array Char) : Array Char :=
sorry

def solve (s : String) : String :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem NoLetters_spec (s : String) (n : Nat) :
n ≤ s.length → NoLetters s n :=
sorry

theorem Reverse_spec (original : Array Char) :
let reversed := Reverse original
reversed.size = original.size ∧
(∀ i, 0 ≤ i ∧ i < original.size →
reversed[i]! = original[original.size - 1 - i]!) :=
sorry

theorem solve_spec (s : String) :
let result := solve s
result.length = s.length ∧
(¬NoLetters s s.length →
(∀ i, 0 ≤ i ∧ i < s.length ∧ IsLetter (s.get ⟨i⟩) →
result.get ⟨i⟩ = ToggleCase (s.get ⟨i⟩)) ∧
(∀ i, 0 ≤ i ∧ i < s.length ∧ ¬IsLetter (s.get ⟨i⟩) →
result.get ⟨i⟩ = s.get ⟨i⟩)) ∧
(NoLetters s s.length → isReverse result s) :=
sorry
-- </vc-theorems>