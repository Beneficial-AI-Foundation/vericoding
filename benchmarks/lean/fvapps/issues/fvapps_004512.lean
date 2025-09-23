-- <vc-preamble>
def User.withdraw (u : User) (amt : Nat) : Option (String × User) := sorry
def User.add_cash (u : User) (amt : Nat) : String × User := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def User.check (u1 : User) (u2 : User) (amt : Nat) : Option (String × User × User) := sorry

theorem user_creation_preserves_fields 
  (name : String) (balance : Nat) (has_checking : Bool) :
  let u := User.mk name balance has_checking
  u.name = name ∧ u.balance = balance ∧ u.checking_account = has_checking := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem withdraw_decreases_balance
  (name : String) (initial_balance withdrawal : Nat) :
  withdrawal ≤ initial_balance →
  let u := User.mk name initial_balance true
  match u.withdraw withdrawal with
  | some (msg, u') => 
      u'.balance = initial_balance - withdrawal ∧
      msg = s!"{name} has {initial_balance - withdrawal}"
  | none => False
  := sorry

theorem withdraw_fails_if_insufficient
  (name : String) (initial_balance withdrawal : Nat) :
  withdrawal > initial_balance →
  let u := User.mk name initial_balance true
  u.withdraw withdrawal = none := sorry

theorem add_cash_increases_balance
  (name : String) (initial_balance deposit : Nat) :
  let u := User.mk name initial_balance true
  let (msg, u') := u.add_cash deposit
  u'.balance = initial_balance + deposit ∧
  msg = s!"{name} has {initial_balance + deposit}" := sorry

theorem check_transfers_amount
  (name1 name2 : String) (balance1 balance2 transfer : Nat) :
  transfer ≤ balance2 →
  let u1 := User.mk name1 balance1 true
  let u2 := User.mk name2 balance2 true
  match u1.check u2 transfer with
  | some (msg, u1', u2') => 
      u1'.balance = balance1 + transfer ∧
      u2'.balance = balance2 - transfer ∧
      msg = s!"{name1} has {balance1 + transfer} and {name2} has {balance2 - transfer}"
  | none => False
  := sorry

theorem check_fails_without_checking
  (name1 name2 : String) (balance1 balance2 transfer : Nat) :
  let u1 := User.mk name1 balance1 true
  let u2 := User.mk name2 balance2 false
  u1.check u2 transfer = none := sorry

theorem check_fails_insufficient_balance
  (name1 name2 : String) (balance1 balance2 transfer : Nat) :
  transfer > balance2 →
  let u1 := User.mk name1 balance1 true
  let u2 := User.mk name2 balance2 true
  u1.check u2 transfer = none := sorry
-- </vc-theorems>