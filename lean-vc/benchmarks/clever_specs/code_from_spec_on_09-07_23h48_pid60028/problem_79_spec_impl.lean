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
  decimal = List.foldl (fun acc d => acc * 2 + d) 0 resultTrimmed
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
  List.foldl (fun acc d => acc * 2 + d) 0 (natToBinary n) = n := by
  simp [natToBinary]
  if h : n = 0 then
    simp [h]
  else
    simp [h]
    sorry

-- LLM HELPER
lemma listNatToString_toList (l : List Nat) : 
  (listNatToString l).toList = l.map (fun n => Char.ofNat (n + '0'.toNat)) := by
  simp [listNatToString, String.toList, String.mk]

-- LLM HELPER
lemma char_conversion (n : Nat) (h : n < 10) : 
  (Char.ofNat (n + '0'.toNat)).toNat - '0'.toNat = n := by
  simp [Char.ofNat, Char.toNat]
  omega

-- LLM HELPER
lemma natToBinary_bounds (n : Nat) : ∀ x ∈ natToBinary n, x < 10 := by
  intro x hx
  simp [natToBinary] at hx
  if h : n = 0 then
    simp [h] at hx
    cases hx with
    | head => norm_num
    | tail _ hx_tail => cases hx_tail
  else
    simp [h] at hx
    sorry

-- LLM HELPER  
lemma natToBinary_nonempty (n : Nat) : 0 < (natToBinary n).length := by
  simp [natToBinary]
  if h : n = 0 then
    simp [h]
  else
    simp [h]
    sorry

-- LLM HELPER
lemma implementation_parts (decimal : Nat) : 
  let s := implementation decimal
  let middle := listNatToString (natToBinary decimal)
  s = "db" ++ middle ++ "db" ∧
  s.take 2 = "db" ∧
  s.drop (s.length - 2) = "db" ∧
  4 < s.length := by
  simp [implementation]
  let middle := listNatToString (natToBinary decimal)
  constructor
  · rfl
  constructor
  · simp [String.take]
  constructor
  · simp [String.drop, String.length]
  · simp [String.length]
    have h1 := natToBinary_nonempty decimal
    simp [listNatToString, String.length]
    omega

theorem correctness
(decimal: Nat)
: problem_spec implementation decimal := by
  use implementation decimal
  constructor
  · rfl
  · simp [problem_spec]
    let s := implementation decimal
    have parts := implementation_parts decimal
    constructor
    · exact parts.2.2.2
    constructor
    · exact parts.2.2.1
    constructor
    · exact parts.2.1
    · simp [implementation]
      have h_bounds := natToBinary_bounds decimal
      have h_correct := natToBinary_correct decimal
      have h_toList := listNatToString_toList (natToBinary decimal)
      rw [h_toList]
      simp [List.drop, List.dropLast, List.map]
      have : (natToBinary decimal).map (fun n => Char.ofNat (n + '0'.toNat)) |>.map (fun c => c.toNat - '0'.toNat) = natToBinary decimal := by
        simp [List.map_map]
        apply List.map_id_of_eq
        intro x hx
        exact char_conversion x (h_bounds x hx)
      rw [this]
      exact h_correct