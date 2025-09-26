-- <vc-preamble>
def String.containsSubstr (s : String) (sub : String) : Bool := sorry

def List.sum (xs : List Int) : Int := 
  match xs with
  | [] => 0
  | x :: rest => x + rest.sum

structure Environment where
  modifiers : List (String × Int)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def total_licks (env : Environment) : String := sorry

theorem total_licks_base_text (env : Environment) :
  let result := total_licks env
  (result.startsWith "It took") ∧ 
  (result.containsSubstr " licks to get to the tootsie roll center of a tootsie pop") :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem total_licks_contains_sum (env : Environment) :
  let expected := 252 + (env.modifiers.map Prod.snd).sum
  let result := total_licks env
  result.containsSubstr (toString expected) :=
sorry

theorem total_licks_toughest_challenge (env : Environment) :
  let maxVal := (env.modifiers.map Prod.snd).maximum?.getD 0
  let result := total_licks env
  if maxVal > 0 then
    (result.containsSubstr "The toughest challenge was") ∧
    (env.modifiers.find? (fun p => p.2 = maxVal)).map (fun p => result.containsSubstr p.1) = some true
  else
    ¬(result.containsSubstr "The toughest challenge was") :=
sorry

theorem total_licks_no_positive_challenges 
  (env : Environment)
  (h : ∀ p ∈ env.modifiers, p.2 ≤ 0) :
  ¬((total_licks env).containsSubstr "The toughest challenge was") :=
sorry

theorem total_licks_always_has_toughest_challenge
  (env : Environment)
  (h1 : env.modifiers.length > 0)
  (h2 : ∀ p ∈ env.modifiers, p.2 > 0) :
  (total_licks env).containsSubstr "The toughest challenge was" :=
sorry

/-
info: 'It took 260 licks to get to the tootsie roll center of a tootsie pop. The toughest challenge was freezing temps.'
-/
-- #guard_msgs in
-- #eval total_licks {"freezing temps": 10, "clear skies": -2}

/-
info: 'It took 245 licks to get to the tootsie roll center of a tootsie pop.'
-/
-- #guard_msgs in
-- #eval total_licks {"happiness": -5, "clear skies": -2}

/-
info: 'It took 512 licks to get to the tootsie roll center of a tootsie pop. The toughest challenge was evil wizards.'
-/
-- #guard_msgs in
-- #eval total_licks {"dragons": 100, "evil wizards": 110, "trolls": 50}
-- </vc-theorems>