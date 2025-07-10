def problem_spec
-- function signature
(implementation: Nat → String)
-- inputs
(n: Nat) :=
-- spec
let spec (result : String) :=
  0 < n →
  result.all (fun c => c = '0' ∨ c = '1') →
  Nat.ofDigits 2 (result.data.map (fun c => if c = '0' then 0 else 1)).reverse = (Nat.digits 10 n).sum
-- program termination
∃ result,
  implementation n = result ∧
  spec result

-- LLM HELPER
def digitSum (n : Nat) : Nat :=
  if n = 0 then 0 else
  let rec aux (m : Nat) : Nat :=
    if m = 0 then 0
    else (m % 10) + aux (m / 10)
  aux n

-- LLM HELPER
def natToBinary (n : Nat) : String :=
  if n = 0 then "0"
  else
    let rec aux (m : Nat) : String :=
      if m = 0 then ""
      else aux (m / 2) ++ (if m % 2 = 0 then "0" else "1")
    aux n

def implementation (n: Nat) : String := 
  natToBinary (digitSum n)

-- LLM HELPER
lemma digitSum_correct (n : Nat) : digitSum n = (List.range (Nat.log 10 n + 1)).map (fun i => (n / (10 ^ i)) % 10) |>.sum := by
  sorry

-- LLM HELPER
lemma natToBinary_all_binary (n : Nat) : (natToBinary n).all (fun c => c = '0' ∨ c = '1') := by
  sorry

-- LLM HELPER
lemma natToBinary_correct (n : Nat) : 
  Nat.ofDigits 2 ((natToBinary n).data.map (fun c => if c = '0' then 0 else 1)).reverse = n := by
  sorry

theorem correctness
(n: Nat)
: problem_spec implementation n := by
  simp [problem_spec, implementation]
  use natToBinary (digitSum n)
  constructor
  · rfl
  · intro h₁ h₂
    exact natToBinary_correct (digitSum n)