/-
For a given 2D vector described by cartesian coordinates of its initial point and terminal point in the following format:

```python
[[x1, y1], [x2, y2]]
```

Your function must return this vector's length represented as a floating point number.

Error must be within 1e-7.

Coordinates can be integers or floating point numbers.
-/

-- <vc-helpers>
-- </vc-helpers>

def vectorLength (p1 p2 : Point) : Float := 
  sorry

theorem vectorLength_nonnegative (p1 p2 : Point) :
  vectorLength p1 p2 ≥ 0 := by
  sorry

theorem vectorLength_symmetric (p1 p2 : Point) :
  vectorLength p1 p2 = vectorLength p2 p1 := by
  sorry

theorem vectorLength_same_point (p : Point) :
  vectorLength p p = 0 := by
  sorry

theorem vectorLength_triangle_inequality (a b c : Point) :
  vectorLength a c ≤ vectorLength a b + vectorLength b c := by
  sorry

-- Apps difficulty: introductory
-- Assurance level: guarded