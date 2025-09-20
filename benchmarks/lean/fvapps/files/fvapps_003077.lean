-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def get_users_ids (s : String) : List String := sorry

theorem get_users_ids_is_list (s : String) :
  ∃ (l : List String), get_users_ids s = l :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem get_users_ids_elements_are_strings (s : String) (x : String) :
  x ∈ get_users_ids s → x.length ≥ 0 :=
sorry

theorem get_users_ids_length (s : String) :
  List.length (get_users_ids s) = List.length (s.split (· == ',')) :=
sorry

theorem get_users_ids_no_uid_prefix (s : String) (x : String) :
  x ∈ get_users_ids s → ∃ i j k, 
    i ≠ j ∧ j ≠ k ∧ i ≠ k ∧
    (¬(x.toLower.get? i = some 'u' ∧
       x.toLower.get? j = some 'i' ∧
       x.toLower.get? k = some 'd')) :=
sorry

theorem get_users_ids_lowercase (s : String) (x : String) :
  x ∈ get_users_ids s → x = x.toLower :=
sorry 

theorem get_users_ids_no_hash (s : String) (x : String) :
  x ∈ get_users_ids s → ∀ i, x.get? i ≠ some '#' :=
sorry
-- </vc-theorems>