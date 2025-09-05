Everyday we go to different places to get our things done. Those places can be represented by specific location points `[ [, ], ... ]` on a map. I will be giving you an array of arrays that contain coordinates of the different places I had been on a particular day. Your task will be to find `peripheries (outermost edges)` of the bounding box that contains all the points. The response should only contain `Northwest and Southeast` points as follows: `{ "nw": [, ], "se": [ , ] }`. You are adviced to draw the points on a 2D plan to visualize:

```
                         N
                         ^
    p(nw)  ______________|________________
          |              |                |
          |              | all other      |   
          |              |  points        |
          |              |                |
     ----------------------------------------> E          
          |              |                |
          |  all other   |                |
          |  points      |                |
          |______________|________________|
                         |                  p(se)
```

def box (coords : List (Float × Float)) : Box :=
  sorry

def minList (l : List Float) : Float :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded