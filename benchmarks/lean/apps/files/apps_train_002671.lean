/-
Implement the [Polybius square cipher](http://en.wikipedia.org/wiki/Polybius_square).

Replace every letter with a two digit number. The first digit is the row number, and the second digit is the column number of following square. Letters `'I'` and `'J'` are both 24 in this cipher:

table#polybius-square {width: 100px;}
table#polybius-square td {background-color: #2f2f2f;}
table#polybius-square th {background-color: #3f3f3f;}

12345
1ABCDE
2FGHI/JK
3LMNOP
4QRSTU
5VWXYZ

Input will be valid (only spaces and uppercase letters from A to Z), so no need to validate them.

## Examples

```python
polybius('A')  # "11"
polybius('IJ') # "2424"
polybius('CODEWARS') # "1334141552114243"
polybius('POLYBIUS SQUARE CIPHER') # "3534315412244543 434145114215 132435231542"
```
-/

-- <vc-helpers>
-- </vc-helpers>

def polybius : String → String :=
  sorry

theorem polybius_output_format (text : String) : 
  (text.data.all (fun c => c.isUpper ∨ c = ' ')) →
  (text.length = (polybius text).length) ∧
  (polybius text).data.all (fun c => c ∈ ['1', '2', '3', '4', '5', ' ']) :=
  sorry

theorem polybius_case_insensitive (text : String) :
  polybius text.toUpper = polybius text.toLower :=
  sorry

theorem polybius_spaces (text : String) :
  text.data.all (fun c => c = ' ') → polybius text = text :=
  sorry

theorem polybius_consistency (text : String) :
  polybius text = polybius text :=
  sorry

theorem polybius_concatenation (text1 text2 : String) :
  polybius (text1 ++ text2) = polybius text1 ++ polybius text2 :=
  sorry

/-
info: '3534315412244543'
-/
-- #guard_msgs in
-- #eval polybius "POLYBIUS"

/-
info: '1334141552114243'
-/
-- #guard_msgs in
-- #eval polybius "CODEWARS"

/-
info: '3534315412244543 434145114215 132435231542'
-/
-- #guard_msgs in
-- #eval polybius "POLYBIUS SQUARE CIPHER"

-- Apps difficulty: introductory
-- Assurance level: unguarded