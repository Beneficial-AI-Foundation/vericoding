-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_uniq (arr : List String) : String := sorry

def String.title (s : String) : String := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_uniq_returns_unique_string 
  {base_str unique_str : String} {copies : Nat}
  (h_copies : copies ≥ 2) 
  (h_base_alph : ∀ c ∈ base_str.toList, c ∈ ['a', 'b', 'c'])
  (h_unique_alph : ∀ c ∈ unique_str.toList, c ∈ ['d', 'e', 'f'])
  : let test_arr := List.replicate copies base_str ++ [unique_str]
    let result := find_uniq test_arr 
    (∀ c ∈ result.toLower.toList, c ∉ base_str.toLower.toList) ∧ 
    result = unique_str := sorry

theorem find_uniq_case_insensitive
  {base_str : String} {copies : Nat}
  (h_copies : copies ≥ 2)
  (h_base_alph : ∀ c ∈ base_str.toList, c ∈ ['a', 'b'])
  : let variations := [base_str, base_str.toUpper, base_str.toLower, base_str.title]
    let unique := String.mk (List.replicate base_str.length 'c')
    let test_arr := List.join (List.replicate copies variations) ++ [unique]
    find_uniq test_arr = unique := sorry

theorem find_uniq_ignores_whitespace
  {base_str : String}
  (h_base_alph : ∀ c ∈ base_str.toList, c.toNat ≥ 65 ∧ c.toNat ≤ 90)
  : let test_arr := [s!" {base_str} ", base_str, s!"{base_str} ", "unique"]
    find_uniq test_arr = "unique" := sorry

/-
info: 'BbBb'
-/
-- #guard_msgs in
-- #eval find_uniq ["Aa", "aaa", "aaaaa", "BbBb", "Aaaa", "AaAaAa", "a"]

/-
info: 'foo'
-/
-- #guard_msgs in
-- #eval find_uniq ["abc", "acb", "bac", "foo", "bca", "cab", "cba"]

/-
info: 'victor'
-/
-- #guard_msgs in
-- #eval find_uniq ["silvia", "vasili", "victor"]
-- </vc-theorems>