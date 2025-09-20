-- <vc-preamble>
def isValidCharacter (c : String) : Bool :=
  match c with
  | "warrior" | "knight" | "wanderer" | "thief" | "bandit"
  | "hunter" | "sorcerer" | "pyromancer" | "cleric" | "deprived" => true
  | _ => false

def isValidBuild (b : List Nat) : Bool :=
  b.length = 8 && b.all (fun x => x ≥ 1 && x ≤ 99)

def baseStats (c : String) : List Nat :=
  match c with
  | "warrior" => [11, 8, 12, 13, 13, 11, 9, 9]
  | "knight" => [14, 10, 10, 11, 11, 10, 9, 11]
  | "wanderer" => [10, 11, 10, 10, 14, 12, 11, 8]
  | "thief" => [9, 11, 9, 9, 15, 10, 12, 11]
  | "bandit" => [12, 8, 14, 14, 9, 11, 8, 10]
  | "hunter" => [11, 9, 11, 12, 14, 11, 9, 9]
  | "sorcerer" => [8, 15, 8, 9, 11, 8, 15, 8]
  | "pyromancer" => [10, 12, 11, 12, 9, 12, 10, 8]
  | "cleric" => [11, 11, 9, 12, 8, 11, 8, 14]
  | "deprived" => [11, 11, 11, 11, 11, 11, 11, 11]
  | _ => []
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def souls (character : String) (build : List Nat) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem souls_returns_valid_string
    {c : String} {b : List Nat}
    (hc : isValidCharacter c = true)
    (hb : isValidBuild b = true) :
    let result := souls c b
    result.startsWith s!"Starting as a {c}" ∧
    ("level" ∈ result.splitOn " ") ∧
    ("will require" ∈ result.splitOn " ") ∧
    result.endsWith "souls." :=
sorry

theorem souls_returns_non_negative_souls
    {c : String} {b : List Nat}
    (hc : isValidCharacter c = true)
    (hb : isValidBuild b = true) :
    let result := souls c b
    let soulsNeeded := result.splitOn "require " |>.get! 1 |>.splitOn " souls" |>.get! 0 |>.toNat!
    soulsNeeded ≥ 0 :=
sorry

theorem zero_change_requires_zero_souls
    {c : String}
    (hc : isValidCharacter c = true) :
    let result := souls c (baseStats c)
    result.endsWith "will require 0 souls." :=
sorry
-- </vc-theorems>