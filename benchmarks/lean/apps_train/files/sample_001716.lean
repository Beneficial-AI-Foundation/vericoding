Let's say you have a bunch of points, and you want to round them all up and calculate the area of the smallest polygon containing all of the points (nevermind why, you just want a challenge). What you're looking for is the area of the *convex hull* of these points. Here is an example, delimited in blue :

## Your task

Implement a function that will compute the area covered by the convex hull that can be formed from an array of points, the area being rounded to two decimal places. The points are given as `(x,y)`, like in an orthonormal coordinates system.

```python
points = [(0, 0), (0, 3), (4, 0)]
convex_hull_area(points) == 6.00
```

*Note* : In Python, the scipy module has a [ready made solution](https://docs.scipy.org/doc/scipy/reference/generated/scipy.spatial.ConvexHull.html) for this. Of course, if you use it here, you are lame.

*P. S.* : If you enjoy this kata, you may also like this one, which asks you to compute a convex hull, without finding its area.

def Point := Float × Float

def convex_hull_area (points : List Point) : Float :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded