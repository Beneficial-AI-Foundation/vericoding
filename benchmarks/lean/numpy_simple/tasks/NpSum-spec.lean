-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sum {n : Nat} (a : Vector Int n) : Int :=
sorry

def sumArray {n : Nat} (a : Vector Int n) (start finish : Nat) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem sum_spec {n : Nat} (a : Vector Int n) :
  sum a = sumArray a 0 n ∧
  ∀ start finish : Nat, start ≤ finish → finish ≤ n →
    sumArray a start finish = (List.range (finish - start)).foldl (fun acc i => acc + a[start + i]'sorry) 0 ∧
  ∀ m n : Nat, ∀ a : Vector Int m, ∀ b : Vector Int n, sum (a ++ b) = sum a + sum b :=
sorry
-- </vc-theorems>