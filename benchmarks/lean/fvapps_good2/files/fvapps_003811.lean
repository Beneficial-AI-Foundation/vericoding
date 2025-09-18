-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def add (a b : Int) : Int :=
sorry

def multiply (a b : Int) : Int :=
sorry

def divide (a b : Int) : Int :=
sorry

def mod (a b : Int) : Int :=
sorry

def exponent (a b : Int) : Int :=
sorry

def subt (a b : Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem add_commutative (a b : Int) : add a b = add b a :=
sorry

theorem add_identity (a : Int) : add a 0 = a :=
sorry

theorem add_associative (a b : Int) : add (add a b) 0 = add a (add b 0) :=
sorry

theorem mult_commutative (a b : Int) : multiply a b = multiply b a :=
sorry

theorem mult_identity (a : Int) : multiply a 1 = a :=
sorry

theorem mult_zero (a : Int) : multiply a 0 = 0 :=
sorry

theorem div_self {a : Int} (h : a ≠ 0) : divide a a = 1 :=
sorry

theorem div_mult_cancel (a b : Int) (h : b ≠ 0) :
  multiply (divide a b) b = a :=
sorry

theorem mod_bounds (a b : Int) (h : b > 0) :
  0 ≤ mod a b ∧ mod a b < b :=
sorry

theorem mod_reconstruction (a b : Int) (h : b ≠ 0) :
  a = multiply (divide a b) b + mod a b :=
sorry

theorem exp_zero (a : Int) (h : a > 0) : exponent a 0 = 1 :=
sorry

theorem exp_one (a : Int) : exponent a 1 = a :=
sorry

theorem exp_growth (a b : Int) (h1 : a > 0) (h2 : b > 0) :
  exponent a b ≥ a :=
sorry

theorem subt_as_add (a b : Int) : subt a b = add a (-b) :=
sorry

theorem subt_self (a : Int) : subt a a = 0 :=
sorry
-- </vc-theorems>