-- <vc-preamble>
def Nat.choose (n k : Nat) : Nat := sorry

def List.sort (l : List Nat) : List Nat := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def transform (arr : List Nat) (x : Nat) : Nat := sorry

theorem transform_single_element (n x : Nat) (h : x ≤ n) :
  transform [n] x = (List.range (n - x + 1)).foldl (fun acc i => acc + Nat.choose (i + x) x) 0 :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem transform_shuffle (arr : List Nat) (x : Nat) (h : ∀ n ∈ arr, n ≥ x) :
  transform arr x = transform (List.sort arr) x :=
sorry 

theorem transform_zero_x (arr : List Nat) :
  transform arr 0 = List.foldl (fun acc n => acc + (n + 1)) 0 arr :=
sorry
-- </vc-theorems>