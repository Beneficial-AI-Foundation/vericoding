Create a function hollow_triangle(height) that returns a hollow triangle of the correct height. The height is passed through to the function and the function should return a list containing each line of the hollow triangle. 
```
hollow_triangle(6) should return : ['_____#_____', '____#_#____', '___#___#___', '__#_____#__', '_#_______#_', '###########']
hollow_triangle(9) should return : ['________#________', '_______#_#_______', '______#___#______', '_____#_____#_____', '____#_______#____', '___#_________#___', '__#___________#__', '_#_____________#_', '#################']
```
The final idea is for the hollow triangle is to look like this if you decide to print each element of the list: 
``` 
hollow_triangle(6) will result in:
_____#_____              1
____#_#____              2
___#___#___              3
__#_____#__              4
_#_______#_              5
###########              6 ---- Final Height

hollow_triangle(9) will result in:
________#________        1
_______#_#_______        2
______#___#______        3
_____#_____#_____        4      
____#_______#____        5
___#_________#___        6
__#___________#__        7
_#_____________#_        8
#################        9 ---- Final Height
```
Pad spaces with underscores i.e _ so each line is the same length.Goodluck and have fun coding !

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded