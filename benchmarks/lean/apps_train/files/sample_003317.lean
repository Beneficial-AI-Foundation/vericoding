In this kata you will be given a sequence of the dimensions of rectangles ( sequence with width and length ) and circles ( radius - just a number ).  
Your task is to return a new sequence of dimensions, sorted ascending by area.

For example,

```python
seq = [ (4.23, 6.43), 1.23, 3.444, (1.342, 3.212) ] # [ rectangle, circle, circle, rectangle ]
sort_by_area(seq) => [ ( 1.342, 3.212 ), 1.23, ( 4.23, 6.43 ), 3.444 ]
```

This kata inspired by [Sort rectangles and circles by area](https://www.codewars.com/kata/sort-rectangles-and-circles-by-area/).

def get_area (x : AreaElement) : Nat :=
  match x with
  | .circle r => 314159 * r * r / 100000  -- π approximation times r^2
  | .rect (w, h) => w * h

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded