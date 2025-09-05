Below is a right-angled triangle:

```
  |\
  | \
  |  \
  |   \ 
o |    \ h 
  |     \
  |    θ \
  |_______\ 
     a
```

Your challange is to write a function (```missingAngle``` in C/C#, ```missing_angle``` in Ruby), that calculates the angle θ in degrees to the nearest integer. You will be given three arguments representing each side: o, h and a. One of the arguments equals zero. Use the length of the two other sides to calculate θ. You will not be expected to handle any erronous data in your solution.

def Float.toDegrees (x : Float) : Float :=
  sorry

def Int.toFloat (x : Int) : Float :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded
