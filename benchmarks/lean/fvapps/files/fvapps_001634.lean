-- <vc-preamble>
def minimum (lst : List Int) : Option Int := lst.foldl (fun min x => match min with
  | none => some x
  | some m => if x < m then some x else some m) none

def maximum (lst : List Int) : Option Int := lst.foldl (fun max x => match max with
  | none => some x
  | some m => if x > m then some x else some m) none
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_min_index (lst : List Int) : Int :=
sorry

def find_max_index (lst : List Int) : Int :=
sorry

def find_second_max (lst : List Int) : Option Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem min_index_empty (lst : List Int) :
  lst = [] → find_min_index lst = -1 :=
sorry

theorem min_index_valid (lst : List Int) (result : Int) :
  result = find_min_index lst →
  result ≠ -1 →
  (∃ min : Int, minimum lst = some min ∧
   0 ≤ result ∧ result < lst.length ∧
   lst.get ⟨result.toNat, sorry⟩ = min ∧
   lst.count min = 1) :=
sorry

theorem min_index_duplicate (lst : List Int) :
  find_min_index lst = -1 →
  lst ≠ [] →
  (∃ min : Int, minimum lst = some min ∧ lst.count min > 1) :=
sorry

theorem max_index_empty (lst : List Int) :
  lst = [] → find_max_index lst = -1 :=
sorry

theorem max_index_valid (lst : List Int) (result : Int) :
  result = find_max_index lst →
  result ≠ -1 →
  (∃ max : Int, maximum lst = some max ∧
   0 ≤ result ∧ result < lst.length ∧
   lst.get ⟨result.toNat, sorry⟩ = max ∧
   lst.count max = 1) :=
sorry

theorem max_index_duplicate (lst : List Int) :
  find_max_index lst = -1 →
  lst ≠ [] →
  (∃ max : Int, maximum lst = some max ∧ lst.count max > 1) :=
sorry

theorem second_max_short (lst : List Int) :
  lst.length < 2 → find_second_max lst = none :=
sorry

theorem second_max_valid (lst : List Int) (result : Int) :
  find_second_max lst = some result →
  (∃ max : Int, maximum lst = some max ∧
   result < max ∧
   (∀ x, x ∈ lst → ¬(result < x ∧ x < max)) ∧
   result ∈ lst) :=
sorry

theorem second_max_none (lst : List Int) :
  find_second_max lst = none →
  lst.length ≥ 2 →
  (∃ x : Int, ∀ y ∈ lst, y = x) :=
sorry

theorem results_from_input (lst : List Int) :
  let min_idx := find_min_index lst
  let max_idx := find_max_index lst
  let second := find_second_max lst
  (min_idx ≠ -1 → (∃ x, lst.get ⟨min_idx.toNat, sorry⟩ = x ∧ x ∈ lst)) ∧
  (max_idx ≠ -1 → (∃ x, lst.get ⟨max_idx.toNat, sorry⟩ = x ∧ x ∈ lst)) ∧
  (second.isSome → (Option.get! second) ∈ lst) :=
sorry
-- </vc-theorems>