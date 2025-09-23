-- <vc-preamble>
def sum_list_nat : List Nat → Nat
  | [] => 0
  | x :: xs => x + sum_list_nat xs
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def bits_war (numbers : List Int) : String :=
sorry

def bitsToCount (n : Int) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem bits_war_returns_valid_result (numbers : List Int) (h : numbers.length > 0) :
  (bits_war numbers = "odds win") ∨
  (bits_war numbers = "evens win") ∨
  (bits_war numbers = "tie") :=
sorry

theorem bits_war_all_zeros (numbers : List Int) :
  (∀ n ∈ numbers, n = 0) →
  bits_war numbers = "tie" :=
sorry

theorem bits_war_all_positive (numbers : List Int) (h : numbers.length > 0) :
  (∀ n ∈ numbers, n ≥ 0) →
  let odd_bits := sum_list_nat ((numbers.filter (fun n => n % 2 = 1)).map bitsToCount)
  let even_bits := sum_list_nat ((numbers.filter (fun n => n % 2 = 0)).map bitsToCount)
  bits_war numbers = if odd_bits > even_bits then "odds win"
                     else if even_bits > odd_bits then "evens win"
                     else "tie" :=
sorry
-- </vc-theorems>