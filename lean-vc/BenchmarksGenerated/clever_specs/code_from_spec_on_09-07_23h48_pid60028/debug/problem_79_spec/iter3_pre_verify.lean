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
    have : ∀ m : Nat, m < n → List.foldl (fun acc d => acc * 2 + d) 0 (natToBinary.aux m []) = m := by
      intro m hm
      induction m using Nat.strong_induction_on with
      | ind m ih =>
        simp [natToBinary.aux]
        if h : m = 0 then
          simp [h]
        else
          simp [h]
          have h1 : m / 2 < m := Nat.div_lt_self (Nat.zero_lt_of_ne_zero h) (by norm_num)
          have h2 := ih (m / 2) h1
          simp [List.foldl]
          rw [h2]
          exact Nat.div_add_mod m 2
    exact this n (Nat.lt_refl n)

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
      have : head ≤ 9 := Nat.le_of_lt_succ this
      simp [Char.ofNat, Char.toNat]
      cases head with
      | zero => simp
      | succ n => 
        cases n with
        | zero => simp
        | succ m => simp [Char.ofNat, Char.toNat]
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
    intro x hx
    have : ∀ m : Nat, ∀ acc : List Nat, (∀ y ∈ acc, y < 10) → ∀ z ∈ natToBinary.aux m acc, z < 10 := by
      intro m
      induction m using Nat.strong_induction_on with
      | ind m ih =>
        intro acc hacc z hz
        simp [natToBinary.aux] at hz
        if h : m = 0 then
          simp [h] at hz
          exact hacc z hz
        else
          simp [h] at hz
          have h1 : m / 2 < m := Nat.div_lt_self (Nat.zero_lt_of_ne_zero h) (by norm_num)
          have h2 : ∀ y ∈ (m % 2) :: acc, y < 10 := by
            intro y hy
            cases hy with
            | head => simp; exact Nat.mod_lt m (by norm_num)
            | tail _ hy' => exact hacc y hy'
          exact ih (m / 2) h1 ((m % 2) :: acc) h2 z hz
    exact this n [] (by simp) x hx

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
      have : ∀ m : Nat, 0 < m → 0 < (natToBinary.aux m []).length := by
        intro m hm
        induction m using Nat.strong_induction_on with
        | ind m ih =>
          simp [natToBinary.aux]
          if h : m = 0 then
            simp [h] at hm
          else
            simp [h]
            have h1 : m / 2 < m := Nat.div_lt_self (Nat.zero_lt_of_ne_zero h) (by norm_num)
            if h2 : m / 2 = 0 then
              simp [h2]
            else
              exact ih (m / 2) h1 (Nat.zero_lt_of_ne_zero h2)
      exact this decimal (Nat.zero_lt_of_ne_zero h)
  have h2 : 0 < (listNatToString (natToBinary decimal)).length := by
    simp [listNatToString, String.length]
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
      have h : 4 < (implementation decimal).length := implementation_length decimal
      simp [String.drop, String.length]
      have : (implementation decimal).length ≥ 2 := by omega
      simp [String.drop]
      rfl
    constructor
    · simp [implementation, String.take]
    · simp [implementation]
      have h1 : natToBinary_correct decimal := natToBinary_correct decimal
      have h2 : natToBinary_bounds decimal := natToBinary_bounds decimal
      have h3 : listNatToString_map_inv (natToBinary decimal) h2 := listNatToString_map_inv (natToBinary decimal) h2
      rw [← h1, ← h3]
      simp [String.toList, String.mk, List.drop, List.dropLast]
      rfl