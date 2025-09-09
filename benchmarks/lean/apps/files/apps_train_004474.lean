-- <vc-helpers>
-- </vc-helpers>

def populate_dict {α β : Type} (keys : List α) (default : β) : List (α × β) := sorry

theorem populate_dict_size {α β : Type} (keys : List α) (default : β) :
  (populate_dict keys default).length = keys.length := sorry

theorem populate_dict_contains_all_keys {α β : Type} (keys : List α) (default : β) :
  ∀ k ∈ keys, k ∈ (populate_dict keys default).map Prod.fst := sorry

theorem populate_dict_all_values_default {α β : Type} (keys : List α) (default : β) :
  ∀ v ∈ (populate_dict keys default).map Prod.snd, v = default := sorry

-- Apps difficulty: introductory
-- Assurance level: guarded