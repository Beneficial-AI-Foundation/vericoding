-- <vc-preamble>
def List.sum (xs : List Nat) : Nat :=
  match xs with
  | [] => 0
  | x :: xs => x + xs.sum

def gcd (a b : Nat) : Nat :=
  sorry

def gcd_list (nums : List Nat) : Nat :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def min_wire_cost (n : Nat) (wire_lengths : List Nat) : Nat × Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem min_wire_cost_divides_all (n : Nat) (wire_lengths : List Nat)
  (h : wire_lengths.length > 0) (h2 : ∀ x ∈ wire_lengths, x > 0) :
  let (result_len, _) := min_wire_cost n wire_lengths
  ∀ w ∈ wire_lengths, w % result_len = 0 :=
sorry 

theorem min_wire_cost_gcd (n : Nat) (wire_lengths : List Nat)  
  (h : wire_lengths.length > 0) (h2 : ∀ x ∈ wire_lengths, x > 0) :
  let (result_len, _) := min_wire_cost n wire_lengths
  result_len = gcd_list wire_lengths :=
sorry

theorem min_wire_cost_preserves_sum (n : Nat) (wire_lengths : List Nat)
  (h : wire_lengths.length > 0) (h2 : ∀ x ∈ wire_lengths, x > 0) :
  let (result_len, result_pieces) := min_wire_cost n wire_lengths
  result_len * result_pieces = wire_lengths.sum :=
sorry

theorem min_wire_cost_even_output (n : Nat) (wire_lengths : List Nat)
  (h : wire_lengths.length > 0) (h2 : ∀ x ∈ wire_lengths, x > 0)
  (h3 : ∀ x ∈ wire_lengths, x % 2 = 0) :
  let (result_len, _) := min_wire_cost n wire_lengths
  result_len % 2 = 0 :=
sorry

theorem min_wire_cost_positive (n : Nat) (wire_lengths : List Nat)
  (h : wire_lengths.length > 0) (h2 : ∀ x ∈ wire_lengths, x > 0) :
  let (result_len, result_pieces) := min_wire_cost n wire_lengths
  result_len > 0 ∧ result_pieces > 0 :=
sorry
-- </vc-theorems>