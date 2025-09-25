-- <vc-preamble>
def Animal.name (a : Animal) : String :=
  match a with
  | mk n => n

def Animal.speak (a : Animal) : String := sorry

inductive Cat where
  | mk (name : String)

def Cat.name (c : Cat) : String :=
  match c with
  | mk n => n
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Cat.speak (c : Cat) : String := sorry

def Cat.toAnimal (c : Cat) : Animal :=
  match c with
  | mk n => Animal.mk n
-- </vc-definitions>

-- <vc-theorems>
theorem animal_speak_format {name : String} (h : name.length > 0) :
  (Animal.mk name).speak = name ++ " speaks." := sorry

theorem cat_speak_format {name : String} (h : name.length > 0) :
  (Cat.mk name).speak = name ++ " meows." := sorry

theorem cat_name_preservation {name : String} (h : name.length > 0) :
  (Cat.mk name).name = name := sorry

theorem cat_is_animal (c : Cat) :
  ∃ (a : Animal), c.toAnimal = a := sorry
-- </vc-theorems>