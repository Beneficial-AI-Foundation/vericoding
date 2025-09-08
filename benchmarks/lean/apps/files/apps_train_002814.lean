/-
# Your Task
You have a cuboid with dimensions x,y,z ∈ ℕ. A subcuboid of this cuboid has dimensions length, width, height ∈ ℕ where 1≤length≤x, 1≤width≤y, 1≤height≤z. If two subcuboids have the same length, width, and height, but they are at different positions within the cuboid, they are distinct. Find the total number of subcuboids for the given cuboid.
# Examples
See sample tests and the image below
### 27 subcuboids for a 2×2×2 cuboid
![subcuboids(2,2,2)](https://i.imgur.com/3CnboOW.jpg)
-/

-- <vc-helpers>
-- </vc-helpers>

def subcuboids (x y z : Nat) : Nat :=
  sorry

theorem cube_symmetry (n : Nat) (h : n > 0) : 
  subcuboids n n n = subcuboids n n n :=
by sorry

theorem dimensions_positive (x y z : Nat) (hx : x > 0) (hy : y > 0) (hz : z > 0) :
  subcuboids x y z > 0 :=
by sorry

theorem dimension_symmetry (x y z : Nat) (hx : x > 0) (hy : y > 0) (hz : z > 0) :
  subcuboids x y z = subcuboids x z y ∧ 
  subcuboids x y z = subcuboids y x z ∧
  subcuboids x y z = subcuboids y z x ∧ 
  subcuboids x y z = subcuboids z x y ∧
  subcuboids x y z = subcuboids z y x :=
by sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval subcuboids 1 1 1

/-
info: 27
-/
-- #guard_msgs in
-- #eval subcuboids 2 2 2

/-
info: 108
-/
-- #guard_msgs in
-- #eval subcuboids 2 3 3

-- Apps difficulty: introductory
-- Assurance level: guarded