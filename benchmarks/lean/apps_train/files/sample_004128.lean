/-
The objective is to disambiguate two given names: the original with another

Let's start simple, and just work with plain ascii strings. 

The function ```could_be``` is given the original name and another one to test
against. 

```python
# should return True if the other name could be the same person 
> could_be("Chuck Norris", "Chuck")
True

# should False otherwise (whatever you may personnaly think)
> could_be("Chuck Norris", "superman")
False
``` 

Let's say your name is *Carlos Ray Norris*, your objective is to return True if
the other given name matches any combinaison of the original fullname:

```python
could_be("Carlos Ray Norris", "Carlos Ray Norris") : True
could_be("Carlos Ray Norris", "Carlos Ray") : True
could_be("Carlos Ray Norris", "Norris") : True
could_be("Carlos Ray Norris", "Norris Carlos") : True
```

For the sake of simplicity:

 * the function is case sensitive and accent sensitive for now
 * it is also punctuation sensitive
 * an empty other name should not match any original
 * an empty orginal name should not be matchable
 * the function is not symmetrical

The following matches should therefore fail:

```python
could_be("Carlos Ray Norris", " ") : False
could_be("Carlos Ray Norris", "carlos") : False
could_be("Carlos Ray Norris", "Norris!") : False
could_be("Carlos Ray Norris", "Carlos-Ray Norris") : False
could_be("Ray Norris", "Carlos Ray Norris") : False
could_be("Carlos", "Carlos Ray Norris") : False
```

Too easy ? Try the next steps: 

* [Author Disambiguation: a name is a Name!](https://www.codewars.com/kata/author-disambiguation-a-name-is-a-name)
* or even harder: [Author Disambiguation: Signatures worth it](https://www.codewars.com/kata/author-disambiguation-signatures-worth-it)
-/

-- <vc-helpers>
-- </vc-helpers>

def could_be (original : String) (another : String) : Bool :=
  sorry

theorem identical_names (name1 name2 : String) :
  name1.trim ≠ "" → name1 = name2 → could_be name1 name2 := by
  sorry

theorem empty_strings (original another : String) :
  another.trim = "" ∨ original = "" → ¬could_be original another := by
  sorry

theorem subset_match (full_name : String) (partial_name : String) :
  partial_name.trim ≠ "" →
  (∀ word, word ∈ (partial_name.split fun c => c = ' ') →
    word ∈ (full_name.split fun c => c = ' ')) →
  could_be full_name partial_name := by
  sorry

theorem reflexive (name : String) :
  name.trim ≠ "" → could_be name name := by
  sorry

theorem case_sensitive :
  ¬could_be "Carlos Ray" "carlos ray" := by
  sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval could_be "Carlos Ray Norris" "Carlos Ray Norris"

/-
info: True
-/
-- #guard_msgs in
-- #eval could_be "Carlos Ray Norris" "Carlos Ray"

/-
info: False
-/
-- #guard_msgs in
-- #eval could_be "" "C"

/-
info: False
-/
-- #guard_msgs in
-- #eval could_be "Carlos Ray Norris" " "

/-
info: False
-/
-- #guard_msgs in
-- #eval could_be "Carlos Ray Norris" "carlos"

-- Apps difficulty: introductory
-- Assurance level: unguarded