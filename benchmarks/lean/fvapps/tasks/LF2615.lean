-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def namelist (names : List (String × String)) : String :=
  sorry

def containsSubstr (s₁ s₂ : String) : Bool :=
  sorry

def String.count (s : String) (c : Char) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem namelist_empty_list :
  namelist [] = "" :=
sorry

theorem namelist_single_name (name : String) :
  namelist [(name, "name")] = name :=
sorry

theorem namelist_multiple_names {n : ℕ} (names : List (String × String))
  (h1 : names.length > 1)
  (h2 : ∀ p ∈ names, p.2 = "name") :
  let result := namelist names;
  let all_names := names.map Prod.fst;

  (∀ name ∈ all_names, containsSubstr result name)

  ∧ containsSubstr result " & "

  ∧ (String.count result ',' = names.length - 2)

  ∧ (result.splitOn " & ").get! 1 = names.getLast?.get!.1 :=
sorry
-- </vc-theorems>