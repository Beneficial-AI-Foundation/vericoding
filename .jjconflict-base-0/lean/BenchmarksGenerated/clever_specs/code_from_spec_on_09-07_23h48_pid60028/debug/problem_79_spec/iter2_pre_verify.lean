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
lemma listNatToString_map_inv (l : List Nat) (h : ∀ x ∈ l, x < 10) :
  (listNatToString l).toList.map (fun c => c.toNat - '0'.toNat) = l := by
  simp [listNatToString]
  induction l with
  | nil => simp
  | cons head tail ih =>
    simp [String.mk, List.map]
    constructor
    · have : head < 10 := h head (List.mem_cons_self head tail)
      simp [Char.ofNat, Char.toNat]
      sorry
    · apply ih
      intros x hx
      exact h x (List.mem_cons_of_mem head hx)

-- LLM HELPER
lemma natToBinary_bounds (n : Nat) : ∀ x ∈ natToBinary n, x < 10 := by
  simp [natToBinary]
  if h : n = 0 then
    simp [h]
    norm_num
  else
    simp [h]
    sorry

-- LLM HELPER
lemma implementation_length (decimal : Nat) : 
  4 < (implementation decimal).length := by
  simp [implementation]
  have h1 : 0 < (natToBinary decimal).length := by
    simp [natToBinary]
    if h : decimal = 0 then
      simp [h]
    else
      simp [h]
      sorry
  have h2 : 0 < (listNatToString (natToBinary decimal)).length := by
    simp [listNatToString]
    exact h1
  simp [String.length]
  omega

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
        have : 4 < (implementation decimal).length := implementation_length decimal
        omega
      simp [String.drop, String.length]
      sorry
    constructor
    · simp [implementation, String.take]
    · simp [implementation]
      have h1 : natToBinary_correct decimal := natToBinary_correct decimal
      have h2 : natToBinary_bounds decimal := natToBinary_bounds decimal
      have h3 : listNatToString_map_inv (natToBinary decimal) h2 := listNatToString_map_inv (natToBinary decimal) h2
      rw [← h1, ← h3]
      simp [String.toList, String.mk]
      sorry