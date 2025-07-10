def problem_spec
(implementation: Nat → Nat → Option String)
(n: Nat) (m: Nat) :=
let spec (result: Option String) :=
  (n > m ↔ result.isNone) ∧
  (n ≤ m ↔ result.isSome) ∧
  (n ≤ m →
    (result.isSome ∧
    let val := Option.getD result "";
    let xs := List.range' n (m+1-n);
    let avg := xs.sum / xs.length;
    (val.take 2 = "0b") ∧
    (Nat.ofDigits 2 ((val.drop 2).toList.map (fun c => c.toNat - '0'.toNat)).reverse = avg)))
∃ result, implementation n m = result ∧
spec result

-- LLM HELPER
def Nat.ofDigits (base : Nat) (digits : List Nat) : Nat :=
  digits.foldr (fun d acc => d + base * acc) 0

-- LLM HELPER
def natToBinary (n: Nat) : String :=
  if n = 0 then "0b0" else
  let rec helper (n: Nat) : String :=
    if n = 0 then ""
    else helper (n / 2) ++ if n % 2 = 0 then "0" else "1"
  "0b" ++ helper n

-- LLM HELPER
lemma natToBinary_correct (n : Nat) : 
  let s := natToBinary n
  s.take 2 = "0b" ∧ 
  Nat.ofDigits 2 ((s.drop 2).toList.map (fun c => c.toNat - '0'.toNat)).reverse = n := by
  unfold natToBinary
  split
  · simp [Nat.ofDigits]
  · simp

def implementation (n: Nat) (m: Nat) : Option String := 
  if n > m then none
  else 
    let xs := List.range' n (m+1-n)
    let avg := xs.sum / xs.length
    some (natToBinary avg)

theorem correctness
(n: Nat) (m: Nat)
: problem_spec implementation n m := by
  unfold problem_spec implementation
  by_cases h : n > m
  · simp [h]
    use none
    constructor
    · simp [h]
    · constructor
      · simp [h]
      · constructor
        · simp [h]
        · intro h_contra
          exact absurd h_contra h
  · push_neg at h
    simp [h]
    let xs := List.range' n (m+1-n)
    let avg := xs.sum / xs.length
    use some (natToBinary avg)
    constructor
    · simp [h]
    · constructor
      · simp [h]
      · constructor
        · simp [h]
        · intro _
          constructor
          · simp
          · simp [Option.getD]
            have correct := natToBinary_correct avg
            constructor
            · exact correct.1
            · exact correct.2