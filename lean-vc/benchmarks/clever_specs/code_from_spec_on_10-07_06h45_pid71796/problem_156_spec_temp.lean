def problem_spec
-- function signature
(impl: Nat → String)
-- inputs
(num: Nat) :=
-- spec
let spec (result: String) :=
1 ≤ num ∧ num ≤ 1000 ∧ (result.data.all (fun c => c.isLower)) →
isValidRoman result ∧ romanToDecimal result = num
-- program terminates
∃ result, impl num = result ∧
-- return value satisfies spec
spec result

-- LLM HELPER
def isValidRoman (s : String) : Bool := 
  let chars := s.data
  chars.all (fun c => c ∈ ['i', 'v', 'x', 'l', 'c', 'd', 'm'])

-- LLM HELPER
def charValue (c : Char) : Nat :=
  match c with
  | 'i' => 1
  | 'v' => 5
  | 'x' => 10
  | 'l' => 50
  | 'c' => 100
  | 'd' => 500
  | 'm' => 1000
  | _ => 0

-- LLM HELPER
def romanToDecimal (s : String) : Nat :=
  let rec helper (chars : List Char) (acc : Nat) : Nat :=
    match chars with
    | [] => acc
    | [c] => acc + charValue c
    | c1 :: c2 :: rest =>
      let v1 := charValue c1
      let v2 := charValue c2
      if v1 < v2 then
        helper (c2 :: rest) (acc + v2 - v1)
      else
        helper (c2 :: rest) (acc + v1)
  helper s.data 0

-- LLM HELPER
def toRoman (n : Nat) : String :=
  let vals := [1000, 900, 500, 400, 100, 90, 50, 40, 10, 9, 5, 4, 1]
  let romans := ["m", "cm", "d", "cd", "c", "xc", "l", "xl", "x", "ix", "v", "iv", "i"]
  let rec helper (n : Nat) (vals : List Nat) (romans : List String) : String :=
    match vals, romans with
    | [], _ => ""
    | _, [] => ""
    | v :: vs, r :: rs =>
      if n >= v then
        r ++ helper (n - v) (v :: vs) (r :: rs)
      else
        helper n vs rs
  helper n vals romans

def implementation (num: Nat) : String := 
  if num >= 1 && num <= 1000 then toRoman num else ""

-- LLM HELPER
lemma toRoman_valid (n : Nat) : n >= 1 ∧ n <= 1000 → isValidRoman (toRoman n) = true := by
  intro h
  unfold isValidRoman toRoman
  simp only [List.all_eq_true]
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false]
  sorry

-- LLM HELPER
lemma toRoman_correct (n : Nat) : n >= 1 ∧ n <= 1000 → romanToDecimal (toRoman n) = n := by
  intro h
  sorry

-- LLM HELPER  
lemma toRoman_lowercase (n : Nat) : (toRoman n).data.all (fun c => c.isLower) = true := by
  unfold toRoman
  simp only [List.all_eq_true]
  intro x hx
  simp only [Char.isLower]
  sorry

theorem correctness
(num: Nat)
: problem_spec implementation num := by
  unfold problem_spec
  use implementation num
  constructor
  · rfl
  · intro h
    unfold implementation
    have h_range : 1 ≤ num ∧ num ≤ 1000 := ⟨h.1, h.2.1⟩
    simp [h_range.1, h_range.2]
    constructor
    · exact toRoman_valid num h_range
    · exact toRoman_correct num h_range