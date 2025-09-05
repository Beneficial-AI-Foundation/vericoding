The aim of this Kata is to write a function which will reverse the case of all consecutive duplicate letters in a string.  That is, any letters that occur one after the other and are identical.

If the duplicate letters are lowercase then they must be set to uppercase, and if they are uppercase then they need to be changed to lowercase. 

**Examples:**
```python
reverse_case("puzzles")    Expected Result: "puZZles"
reverse_case("massive")    Expected Result: "maSSive"
reverse_case("LITTLE")     Expected Result: "LIttLE"
reverse_case("shhh")       Expected Result: "sHHH"
```

Arguments passed will include only alphabetical letters A–Z or a–z.

def reverse (s : String) : String := sorry

theorem reverse_preserves_length (s : String) :
  (reverse s).length = s.length := sorry

def IsRepeatStart (s : String) (i : String.Pos) : Prop :=
  i = ⟨0⟩ ∨ s.get (String.Pos.mk (i.1 - 1)) = s.get i

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
