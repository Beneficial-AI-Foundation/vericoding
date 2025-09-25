-- <vc-preamble>
def charToInt (c : Char) : Int := c.toNat - '0'.toNat

def isLucky (digits : List Int) : Bool :=
  if digits.length = 6 then
    let sum1 := digits[0]! + digits[1]! + digits[2]!
    let sum2 := digits[3]! + digits[4]! + digits[5]!
    sum1 = sum2
  else false

def ValidTicket (ticket : String) : Prop :=
  ticket.length = 6 ∧ ∀ i, i < ticket.length → '0' ≤ ticket.data[i]! ∧ ticket.data[i]! ≤ '9'

def canMakeLuckyWith0Changes (digits : List Int) : Prop :=
  digits.length = 6 ∧ (∀ i, i < digits.length → 0 ≤ digits[i]! ∧ digits[i]! ≤ 9) → isLucky digits

def canMakeLuckyWith1Change (digits : List Int) : Prop :=
  digits.length = 6 ∧ (∀ i, i < digits.length → 0 ≤ digits[i]! ∧ digits[i]! ≤ 9) →
  ∃ pos newDigit, 0 ≤ pos ∧ pos < 6 ∧ 0 ≤ newDigit ∧ newDigit ≤ 9 ∧
    let newDigits := (digits.take pos) ++ [newDigit] ++ (digits.drop (pos + 1))
    isLucky newDigits

def canMakeLuckyWith2Changes (digits : List Int) : Prop :=
  digits.length = 6 ∧ (∀ i, i < digits.length → 0 ≤ digits[i]! ∧ digits[i]! ≤ 9) →
  ∃ i j k l, 0 ≤ j ∧ j < i ∧ i < 6 ∧ 0 ≤ k ∧ k ≤ 9 ∧ 0 ≤ l ∧ l ≤ 9 ∧
    let newDigits := (digits.take i) ++ [k] ++ (digits.drop (i + 1))
    let finalDigits := (newDigits.take j) ++ [l] ++ (newDigits.drop (j + 1))
    isLucky finalDigits

@[reducible, simp]
def solve_precond (ticket : String) : Prop :=
  ValidTicket ticket
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (ticket : String) (h_precond : solve_precond ticket) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (ticket : String) (result : Int) (h_precond : solve_precond ticket) : Prop :=
  let digits := (List.range 6).map (fun i => charToInt (ticket.data[i]!))
  0 ≤ result ∧ result ≤ 3 ∧
  (result = 0 ↔ canMakeLuckyWith0Changes digits) ∧
  (result = 1 ↔ (¬canMakeLuckyWith0Changes digits ∧ canMakeLuckyWith1Change digits)) ∧
  (result = 2 ↔ (¬canMakeLuckyWith0Changes digits ∧ ¬canMakeLuckyWith1Change digits ∧ canMakeLuckyWith2Changes digits)) ∧
  (result = 3 ↔ (¬canMakeLuckyWith0Changes digits ∧ ¬canMakeLuckyWith1Change digits ∧ ¬canMakeLuckyWith2Changes digits))

theorem solve_spec_satisfied (ticket : String) (h_precond : solve_precond ticket) :
    solve_postcond ticket (solve ticket h_precond) h_precond := by
  sorry
-- </vc-theorems>