-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def get_digits (n : Nat) : List Nat :=
sorry

def is_narc (n : Nat) : Bool :=
sorry

def is_narcissistic : List String → Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem get_digits_correct (n : Nat) :
  get_digits n = (toString n).toList.map (fun c => c.toString.toNat!) :=
sorry

theorem is_narc_sum_pow_digits (n : Nat) :
  is_narc n = (n = ((get_digits n).map (fun d => d ^ (get_digits n).length)).foldl (· + ·) 0) :=
sorry

theorem is_narcissistic_all (values : List String) :
  is_narcissistic values = values.all (fun x =>
    if let some n := x.toNat? then
      is_narc n
    else
      false) :=
sorry

theorem non_numeric_returns_false (s : String) :
  ¬s.all Char.isDigit → ¬is_narcissistic [s] :=
sorry
-- </vc-theorems>