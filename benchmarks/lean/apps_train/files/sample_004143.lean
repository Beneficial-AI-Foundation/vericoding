A generalization of Bézier surfaces, called the S-patch, uses an interesting scheme for indexing its control points.

In the case of an n-sided surface of degree d, each index has n non-negative integers that sum to d, and all possible configurations are used.

For example, for a 3-sided quadratic (degree 2) surface the control points are:

> indices 3 2 => [[0,0,2],[0,1,1],[0,2,0],[1,0,1],[1,1,0],[2,0,0]]

Given the degree and the number of sides, generate all control point indices.
The order of the indices in the list can be arbitrary, so for the above example

> [[1,1,0],[2,0,0],[0,0,2],[0,2,0],[0,1,1],[1,0,1]]

is also a good solution.

def indices (n d : Nat) : List (List (List Nat)) := sorry

def sumIndices (idx : List (List Nat)) : Nat := sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded