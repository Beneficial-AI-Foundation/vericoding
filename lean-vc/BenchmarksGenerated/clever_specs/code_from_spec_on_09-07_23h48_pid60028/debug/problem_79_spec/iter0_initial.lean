def problem_spec
-- function signature
(implementation: Nat → String)
-- inputs
(decimal: Nat) :=
-- spec
let spec (result: String) :=
  4 < result.length ∧
  result.drop (result.length - 2) = "db" ∧
  result.take 2 = "db" ∧
  let resultTrimmed := (result.toList.drop 2).dropLast.dropLast.map (fun c => c.toNat - '0'.toNat)
  decimal = Nat.ofDigits 2 resultTrimmed.reverse
-- program termination
∃ result, implementation decimal = result ∧
spec result

-- LLM HELPER
def natToBinary (n : Nat) : List Nat :=
  if n = 0 then [0]
  else
    let rec aux (m : Nat) (acc : List Nat) : List Nat :=
      if m = 0 then acc
      else aux (m / 2) ((m % 2) :: acc)
    aux n []

-- LLM HELPER
def listNatToString (l : List Nat) : String :=
  String.mk (l.map (fun n => Char.ofNat (n + '0'.toNat)))

def implementation (decimal: Nat) : String := 
  "db" ++ listNatToString (natToBinary decimal) ++ "db"

-- LLM HELPER
lemma natToBinary_correct (n : Nat) : 
  Nat.ofDigits 2 (natToBinary n).reverse = n := by
  sorry

-- LLM HELPER
lemma listNatToString_map_inv (l : List Nat) (h : ∀ x ∈ l, x < 10) :
  (listNatToString l).toList.map (fun c => c.toNat - '0'.toNat) = l := by
  sorry

-- LLM HELPER
lemma natToBinary_bounds (n : Nat) : ∀ x ∈ natToBinary n, x < 10 := by
  sorry

-- LLM HELPER
lemma implementation_length (decimal : Nat) : 
  4 < (implementation decimal).length := by
  sorry

theorem correctness
(decimal: Nat)
: problem_spec implementation decimal := by
  use implementation decimal
  constructor
  · rfl
  · constructor
    · exact implementation_length decimal
    constructor
    · simp [implementation]
      have h : (implementation decimal).length ≥ 4 := by
        simp [implementation]
        sorry
      simp [String.drop]
      sorry
    constructor
    · simp [implementation, String.take]
    · simp [implementation]
      have h1 : natToBinary_correct decimal := natToBinary_correct decimal
      have h2 : natToBinary_bounds decimal := natToBinary_bounds decimal
      have h3 : listNatToString_map_inv (natToBinary decimal) h2 := listNatToString_map_inv (natToBinary decimal) h2
      rw [← h1, ← h3]
      sorry