/-
Given an array (arr) as an argument complete the function `countSmileys` that should return the total number of smiling faces.  

Rules for a smiling face:
- Each smiley face must contain a valid pair of eyes. Eyes can be marked as `:` or `;`
- A smiley face can have a nose but it does not have to. Valid characters for a nose are `-` or `~`
- Every smiling face must have a smiling mouth that should be marked with either `)` or `D`

No additional characters are allowed except for those mentioned.  

**Valid smiley face examples:** `:) :D ;-D :~)`  
**Invalid smiley faces:**  `;( :> :} :]`

## Example

```
countSmileys([':)', ';(', ';}', ':-D']);       // should return 2;
countSmileys([';D', ':-(', ':-)', ';~)']);     // should return 3;
countSmileys([';]', ':[', ';*', ':$', ';-D']); // should return 1;
```

## Note

In case of an empty array return 0. You will not be tested with invalid input (input will always be an array). Order of the face (eyes, nose, mouth) elements will always be the same.
-/

-- <vc-helpers>
-- </vc-helpers>

def validSmiley (s : String) : Bool := sorry
def countSmileys (arr : List String) : Nat := sorry

theorem count_matches_valid_check {arr : List String} :
  countSmileys arr = (arr.filter validSmiley).length := sorry

theorem count_is_nonnegative {arr : List String} :
  countSmileys arr ≥ 0 := sorry

theorem count_bounded_by_length {arr : List String} :
  countSmileys arr ≤ arr.length := sorry

/-
info: 0
-/
-- #guard_msgs in
-- #eval count_smileys []

/-
info: 4
-/
-- #guard_msgs in
-- #eval count_smileys [":D", ":~)", ";~D", ":)"]

/-
info: 1
-/
-- #guard_msgs in
-- #eval count_smileys [";]", ":[", ";*", ":$", ";-D"]

-- Apps difficulty: introductory
-- Assurance level: unguarded