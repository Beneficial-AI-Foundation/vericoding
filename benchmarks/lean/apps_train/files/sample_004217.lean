There are some stones on Bob's table in a row, and each of them can be red, green or blue, indicated by the characters `R`, `G`, and `B`.

Help Bob find the minimum number of stones he needs to remove from the table so that the stones in each pair of adjacent stones have different colours.

Examples:

```
"RGBRGBRGGB"   => 1
"RGGRGBBRGRR"  => 3
"RRRRGGGGBBBB" => 9
```

def Stone := Char 

def isRGBChar (c : Char) : Prop :=
  c = 'R' ∨ c = 'G' ∨ c = 'B'

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded