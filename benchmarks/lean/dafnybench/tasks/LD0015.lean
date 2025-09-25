-- <vc-preamble>
inductive Tree where
| Empty : Tree
| Node : Tree → Int → Tree → Tree
deriving Repr
def maxValue : Tree → Int → Prop
| Tree.Empty, _ => True
| Tree.Node left v right, max =>
max > v ∧ maxValue left max ∧ maxValue right max
def minValue : Tree → Int → Prop
| Tree.Empty, _ => True
| Tree.Node left v right, min =>
min < v ∧ minValue left min ∧ minValue right min
def getValue : Tree → Int
| Tree.Empty => 0
| Tree.Node _ v _ => v
def BinarySearchTree : Tree → Prop
| Tree.Empty => True
| Tree.Node left value right =>
(left = Tree.Empty ∨ value > getValue left) ∧
(right = Tree.Empty ∨ value < getValue right) ∧
BinarySearchTree left ∧ BinarySearchTree right ∧
maxValue left value ∧ minValue right value
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def insertRecursion (tree : Tree) (value : Int) : Tree :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem insertRecursion_spec (tree : Tree) (value : Int) :
BinarySearchTree tree →
let res := insertRecursion tree value
res ≠ Tree.Empty → BinarySearchTree res ∧
(∀ x, minValue tree x ∧ x < value → minValue res x) ∧
(∀ x, maxValue tree x ∧ x > value → maxValue res x) :=
sorry
-- </vc-theorems>