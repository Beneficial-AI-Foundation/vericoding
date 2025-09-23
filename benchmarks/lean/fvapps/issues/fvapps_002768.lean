-- <vc-preamble>
def flatten {α : Type} [ToString α] (d : Dict α (Dict α String)) : Dict α String :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def appendPath (s1 s2 : String) : String :=
  s1 ++ "/" ++ s2

structure isFlat (d : Dict String String) : Prop where
  flat : ∀ k v, d.get k = some v → ¬∃ k' v', k = appendPath k' v'
-- </vc-definitions>

-- <vc-theorems>
theorem flatten_flat_dict_unchanged {d : Dict String String} :
  isFlat d → d = Dict.mk (λ s => d.get s) :=
  sorry

theorem flatten_nested_dict (d : Dict String (Dict String String))
    (outer inner : String) (value : String) :
  (d.get outer >>= (λ innerDict => innerDict.get inner)) = some value →
  (flatten d).get (appendPath outer inner) = some value :=
  sorry

theorem flatten_empty_dict :
  flatten (Dict.mk (λ (_ : String) => none)) = Dict.mk (λ (_ : String) => none) :=
  sorry

theorem flatten_empty_nested_dict :
  flatten (Dict.mk (λ s => if s = "key" 
    then some (Dict.mk (λ (_ : String) => none)) 
    else none)) =
  Dict.mk (λ s => if s = "key" then some "" else none) :=
  sorry

/-
info: {'key': 'value'}
-/
-- #guard_msgs in
-- #eval flatten {"key": "value"}

/-
info: {'key/deeper/more/enough': 'value'}
-/
-- #guard_msgs in
-- #eval flatten {"key": {"deeper": {"more": {"enough": "value"}}}}

/-
info: {'empty': ''}
-/
-- #guard_msgs in
-- #eval flatten {"empty": {}}

/-
info: expected
-/
-- #guard_msgs in
-- #eval flatten {"name": {"first": "One", "last": "Drone"}, "job": "scout", "recent": {}, "additional": {"place": {"zone": "1", "cell": "2"}}}
-- </vc-theorems>