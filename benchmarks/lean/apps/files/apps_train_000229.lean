/-
In a N x N grid composed of 1 x 1 squares, each 1 x 1 square consists of a /, \, or blank space.  These characters divide the square into contiguous regions.
(Note that backslash characters are escaped, so a \ is represented as "\\".)
Return the number of regions.

Example 1:
Input:
[
  " /",
  "/ "
]
Output: 2
Explanation: The 2x2 grid is as follows:

Example 2:
Input:
[
  " /",
  "  "
]
Output: 1
Explanation: The 2x2 grid is as follows:

Example 3:
Input:
[
  "\\/",
  "/\\"
]
Output: 4
Explanation: (Recall that because \ characters are escaped, "\\/" refers to \/, and "/\\" refers to /\.)
The 2x2 grid is as follows:

Example 4:
Input:
[
  "/\\",
  "\\/"
]
Output: 5
Explanation: (Recall that because \ characters are escaped, "/\\" refers to /\, and "\\/" refers to \/.)
The 2x2 grid is as follows:

Example 5:
Input:
[
  "//",
  "/ "
]
Output: 3
Explanation: The 2x2 grid is as follows:

Note:

1 <= grid.length == grid[0].length <= 30
grid[i][j] is either '/', '\', or ' '.
-/

-- <vc-helpers>
-- </vc-helpers>

def regions_by_slashes (grid: List String) : Nat :=
  sorry

theorem regions_always_positive
  (grid: List String)
  : regions_by_slashes grid > 0 :=
  sorry 

theorem regions_bounded_by_size
  (grid: List String)
  (h: grid.length = n)
  : regions_by_slashes grid ≤ 4 * n * n :=
  sorry

theorem empty_grid_one_region
  (grid: List String)
  (h1: grid.length > 0)
  (h2: ∀ row ∈ grid, row = (String.mk $ List.replicate 10 ' '))
  : regions_by_slashes grid = 1 :=
  sorry

theorem quotes_irrelevant
  (grid: List String)
  (quoted: List String)
  (h: quoted = grid.map (fun row => "\"" ++ row ++ "\""))
  : regions_by_slashes grid = regions_by_slashes quoted :=
  sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval regions_by_slashes [" /", "/ "]

/-
info: 4
-/
-- #guard_msgs in
-- #eval regions_by_slashes ["\\/", "/\\"]

/-
info: 3
-/
-- #guard_msgs in
-- #eval regions_by_slashes ["//", "/ "]

-- Apps difficulty: interview
-- Assurance level: unguarded