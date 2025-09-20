-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def arith_seq_elements (a r n : Int) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem empty_sequence :
  ∀ (a r : Int),
  arith_seq_elements a r 0 = "" :=
sorry

theorem sequence_start :
  ∀ (a r : Int) (n : Int),
  n > 0 →
  arith_seq_elements a r n ≠ "" ∧
  (String.split (arith_seq_elements a r n) (fun x => x == ',')).get! 0 = toString a :=
sorry

theorem sequence_differences :
  ∀ (a r : Int) (n : Int),
  n > 1 →
  let nums := String.split (arith_seq_elements a r n) (fun x => x == ',')
  ∀ i : Nat,
  i < nums.length - 1 →
  String.toInt! (nums.get! (i+1)) - String.toInt! (nums.get! i) = r :=
sorry

theorem sequence_length :
  ∀ (a r : Int) (n : Int),
  n > 0 →
  (String.split (arith_seq_elements a r n) (fun x => x == ',')).length = n.toNat :=
sorry

theorem zero_difference :
  ∀ (a : Int) (n : Int),
  n > 0 →
  arith_seq_elements a 0 n = String.intercalate ", " (List.replicate n.toNat (toString a)) :=
sorry
-- </vc-theorems>