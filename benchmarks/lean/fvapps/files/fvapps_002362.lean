-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def numSpecialEquivGroups (strings : List String) : Nat :=
  sorry

def isSpecialEquivalent (s1 s2 : String) : Bool :=
  sorry

def belongsToGroup (s : String) (g : Nat) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem num_groups_bounded (strings : List String) :
  1 ≤ numSpecialEquivGroups strings ∧ numSpecialEquivGroups strings ≤ strings.length :=
sorry

theorem special_equiv_same_group (s1 s2 : String) :
  isSpecialEquivalent s1 s2 = true →
  ∃ g, belongsToGroup s1 g = true ∧ belongsToGroup s2 g = true :=
sorry

theorem unique_strings_bound (strings : List String) (h : strings.Nodup) :
  numSpecialEquivGroups strings ≤ strings.length :=
sorry

theorem permutation_invariant (strings : List String) :
  numSpecialEquivGroups strings = numSpecialEquivGroups strings.reverse :=
sorry
-- </vc-theorems>