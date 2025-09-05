An array is defined to be `inertial`if the following conditions hold:
```
a. it contains at least one odd value  
b. the maximum value in the array is even 
c. every odd value is greater than every even value that is not the maximum value.
```
eg:-
```
So [11, 4, 20, 9, 2, 8] is inertial because 
a. it contains at least one odd value [11,9] 
b. the maximum value in the array is 20 which is even 
c. the two odd values (11 and 9) are greater than all the even values that are not equal to 20 (the maximum), i.e., [4, 2, 8]
```
Write a function called `is_inertial` that accepts an integer array and returns `true` if the array is inertial; otherwise it returns `false`.

def isInertial (arr : List Int) : Bool := sorry

def maximum? : List Int → Option Int
  | [] => none
  | x::xs => some (xs.foldl max x)

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
