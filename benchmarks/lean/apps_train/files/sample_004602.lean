# Context

According to Wikipedia : "The seventh son of a seventh son is a concept from folklore regarding special powers given to, or held by, such a son. **The seventh son must come from an unbroken line with no female siblings born between, and be, in turn, born to such a seventh son.**"

# Your task

You will be given a string of JSON, consisting of a family tree containing people's names, genders and children. Your task will be to find the seventh sons of seventh sons in the family tree, and return a __set__ of their names. If there are none, return an __empty set__.

## Tips

* Have a good look at the sample test cases.

* For a seventh son to be a seventh son, there must not be any daughters in the line leading to him. There may be daughters after him, though.

* **You may want to use the json module for this one.**

def Set (α : Type) := α → Prop

def find_seventh_sons_of_seventh_sons (json : String) : Set String :=
  sorry

def fromJson? (s : String) : Option Person :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
