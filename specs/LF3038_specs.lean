-- <vc-preamble>
def conjugate (verb : String) : String × Conjugations :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def SUFFIXES : Char × List String :=
  sorry

-- Properties:
-- </vc-definitions>

-- <vc-theorems>
theorem conjugate_returns_single_entry (verb : String) 
  (h : ∃ stem suffix, verb = stem ++ suffix ∧ String.length suffix = 2) :
  let (key, result) := conjugate verb
  key = verb := sorry

theorem conjugate_returns_six_forms (verb : String)
  (h : ∃ stem suffix, verb = stem ++ suffix ∧ String.length suffix = 2) :
  let (_, result) := conjugate verb
  List.length result.forms = 6 := sorry

theorem conjugations_use_stem (verb : String)
  (h : ∃ stem suffix, verb = stem ++ suffix ∧ String.length suffix = 2) :
  let stem := String.dropRight verb 2
  let (_, result) := conjugate verb
  ∀ conj ∈ result.forms, String.isPrefixOf stem conj := sorry

theorem conjugations_match_suffixes (verb : String)
  (h : ∃ stem suffix, verb = stem ++ suffix ∧ String.length suffix = 2) :
  let stem := String.dropRight verb 2
  let (_, result) := conjugate verb
  let suffixes := List.map (fun conj => String.drop conj (String.length stem)) result.forms 
  suffixes = SUFFIXES.2 := sorry

theorem suffix_patterns_properties (ending : Char) 
  (h : ending = 'a' ∨ ending = 'e' ∨ ending = 'i') :
  List.length SUFFIXES.2 = 6 ∧ 
  String.endsWith (List.getLast SUFFIXES.2 sorry) "n" := sorry

/-
info: {'caminar': ['camino', 'caminas', 'camina', 'caminamos', 'caminais', 'caminan']}
-/
-- #guard_msgs in
-- #eval conjugate "caminar"

/-
info: {'comer': ['como', 'comes', 'come', 'comemos', 'comeis', 'comen']}
-/
-- #guard_msgs in
-- #eval conjugate "comer"

/-
info: {'vivir': ['vivo', 'vives', 'vive', 'vivimos', 'vivis', 'viven']}
-/
-- #guard_msgs in
-- #eval conjugate "vivir"
-- </vc-theorems>