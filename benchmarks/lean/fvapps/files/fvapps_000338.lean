-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def contains_permutation (s1 s2 : String) : Bool :=
  sorry

def IsPermutation (s1 s2 : String) : Prop :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem contains_permutation_empty_string {s : String} :
  contains_permutation "" s = true :=
sorry

theorem contains_permutation_shorter_string {s1 s2 : String} :
  s2.length < s1.length → contains_permutation s1 s2 = false :=
sorry

theorem contains_permutation_self {s : String} :
  contains_permutation s s = true :=
sorry

theorem contains_permutation_concat {s : String} :
  contains_permutation s (s ++ s) = true :=
sorry

theorem contains_permutation_permutation_invariant {s1 s2 s1_perm : String} :
  IsPermutation s1 s1_perm →
  contains_permutation s1 s2 = contains_permutation s1_perm s2 :=
sorry

theorem contains_permutation_single_char {c : Char} {s : String} :
  contains_permutation (String.mk [c]) s = String.contains s c :=
sorry
-- </vc-theorems>