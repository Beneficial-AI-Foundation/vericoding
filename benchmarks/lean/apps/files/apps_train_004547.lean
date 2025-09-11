-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def search_names (logins : List (String × String)) : List (String × String) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem search_names_subset (logins : List (String × String)) :
  ∀ x, x ∈ search_names logins → x ∈ logins :=
  sorry

theorem search_names_all_underscore (logins : List (String × String)) :
  ∀ x ∈ search_names logins, x.1.endsWith "_" :=
  sorry

theorem search_names_contains_all_matching (logins : List (String × String)) :
  (search_names logins).length = 
    (logins.filter (fun x => x.1.endsWith "_")).length :=
  sorry

theorem search_names_preserves_order (logins : List (String × String)) :
  search_names logins = logins.filter (fun x => x.1.endsWith "_") :=
  sorry

theorem search_names_empty_input :
  search_names [] = [] :=
  sorry

theorem search_names_no_matching (logins : List (String × String)) :
  (∀ x ∈ logins, ¬x.1.endsWith "_") →
  search_names logins = [] :=
  sorry

/-
info: [['bar_', 'bar@bar.com']]
-/
-- #guard_msgs in
-- #eval search_names [["foo", "foo@foo.com"], ["bar_", "bar@bar.com"]]

/-
info: [['foo_', 'foo@foo.com'], ['bar_', 'bar@bar.com']]
-/
-- #guard_msgs in
-- #eval search_names [["foo_", "foo@foo.com"], ["bar_", "bar@bar.com"], ["baz", "baz@baz.com"]]

/-
info: []
-/
-- #guard_msgs in
-- #eval search_names [["foo", "foo@foo.com"], ["bar", "bar@bar.com"]]
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded