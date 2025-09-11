-- <vc-preamble>
def check_possible_partition (n k : Nat) (arr : List Nat) : Option (List Nat) := sorry

def getPrefixSums (arr : List Nat) (sizes : List Nat) : List Nat := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sumList : List Nat → Nat
  | [] => 0
  | x::xs => x + sumList xs
-- </vc-definitions>

-- <vc-theorems>
theorem validate_partition_properties {n k : Nat} {arr : List Nat} 
  (h1 : k ≤ n)
  (h2 : 0 < sumList arr) :
  match check_possible_partition n k arr with
  | none => True 
  | some result =>
    -- Length matches k
    result.length = k ∧
    -- Sizes sum to n
    sumList result = n ∧
    -- All partitions have same sum
    let partitions := getPrefixSums arr result;
    match partitions with
    | [] => True
    | hd::_ => List.all partitions (fun x => x = hd) := sorry

theorem impossible_partition {arr : List Nat}
  (h : 0 < arr.length) :
  check_possible_partition arr.length (arr.length + 1) arr = none := sorry
-- </vc-theorems>

-- Apps difficulty: competition
-- Assurance level: guarded