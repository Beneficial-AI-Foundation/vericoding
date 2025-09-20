-- <vc-preamble>
def List.find (p : α → Bool) : List α → Option α
  | [] => none
  | a :: as => if p a then some a else find p as

structure TestMap (α β : Type) where
  toList : List (α × β)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def my_languages (results : TestMap String Nat) : List String := sorry

theorem my_languages_return_type (results : TestMap String Nat) :
  my_languages results |>.all (λ x => String.isPrefixOf x x) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem my_languages_scores_above_threshold (results : TestMap String Nat) 
    (lang : String) (h : lang ∈ my_languages results) :
  ∀ pair ∈ results.toList, pair.1 = lang → pair.2 ≥ 60 := sorry

theorem my_languages_all_qualifying_included (results : TestMap String Nat) :
  (my_languages results).length = 
    (results.toList.filter (λ p => p.2 ≥ 60)).length := sorry

theorem my_languages_sorted (results : TestMap String Nat) 
    (i : Nat) (h : i + 1 < (my_languages results).length) :
  let output := my_languages results
  ∀ pair1, ∀ pair2,
    pair1 ∈ results.toList →
    pair2 ∈ results.toList →
    pair1.1 = output[i]! →
    pair2.1 = output[i+1]! →
    pair1.2 ≥ pair2.2 := sorry

theorem my_languages_empty_below_threshold (results : TestMap String Nat)
    (h : ∀ p ∈ results.toList, p.2 < 60) :
  my_languages results = [] := sorry

theorem my_languages_all_included_above_threshold (results : TestMap String Nat)
    (h : ∀ p ∈ results.toList, p.2 ≥ 60) :
  (my_languages results).length = results.toList.length := sorry
-- </vc-theorems>