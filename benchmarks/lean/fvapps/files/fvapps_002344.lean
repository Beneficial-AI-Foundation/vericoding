-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def to_hex (n : Int) : String :=
sorry

def hexToNat (s : String) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem to_hex_positive_integers (n : Nat) (h : n < 2^32) :
  let result := to_hex n
  (hexToNat result = n) ∧
  (result.length ≤ 8) ∧
  (∀ c ∈ result.data, c ∈ ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9', 'a', 'b', 'c', 'd', 'e', 'f']) :=
sorry

theorem to_hex_negative_integers (n : Int) (h1 : -(2^31) ≤ n) (h2 : n < 0) :
  let result := to_hex n
  (result.length = 8) ∧
  (∀ c ∈ result.data, c ∈ ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9', 'a', 'b', 'c', 'd', 'e', 'f']) ∧
  (let value := hexToNat result
   if value ≥ 2^31 then
     value - 2^32 = n
   else
     value = n) :=
sorry

theorem to_hex_zero :
  to_hex 0 = "0" :=
sorry

theorem to_hex_length (n : Int) :
  let result := to_hex n
  1 ≤ result.length ∧ result.length ≤ 8 :=
sorry
-- </vc-theorems>