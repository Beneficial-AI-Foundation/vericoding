


/-!
{
"name": "BinarySearchTree_tmp_tmp_bn2twp5_bst4copy_insert",
"category": "Dafny Translation",
"description": "Automatically translated from Dafny specification: BinarySearchTree_tmp_tmp_bn2twp5_bst4copy_insert",
"source": "Dafny",
"translation_date": "2024",
"functions": ,
"methods":
}
-/


/-- Binary search tree datatype -/
inductive Tree where
| Empty : Tree
| Node : Tree → Int → Tree → Tree
deriving Repr



/-- Predicate ensuring all values in tree are less than max -/
def maxValue : Tree → Int → Prop
| Tree.Empty, _ => True
| Tree.Node left v right, max =>
max > v ∧ maxValue left max ∧ maxValue right max

/-- Predicate ensuring all values in tree are greater than min -/
def minValue : Tree → Int → Prop
| Tree.Empty, _ => True
| Tree.Node left v right, min =>
min < v ∧ minValue left min ∧ minValue right min

/-- Helper function to get value from a tree node -/
def getValue : Tree → Int
| Tree.Empty => 0
| Tree.Node _ v _ => v

/-- Predicate defining a valid binary search tree -/
def BinarySearchTree : Tree → Prop
| Tree.Empty => True
| Tree.Node left value right =>
(left = Tree.Empty ∨ value > getValue left) ∧
(right = Tree.Empty ∨ value < getValue right) ∧
BinarySearchTree left ∧ BinarySearchTree right ∧
maxValue left value ∧ minValue right value

/-- Recursive insertion into binary search tree -/
def insertRecursion (tree : Tree) (value : Int) : Tree := sorry

/-- Specification for recursive insertion -/
theorem insertRecursion_spec (tree : Tree) (value : Int) :
BinarySearchTree tree →
let res := insertRecursion tree value
res ≠ Tree.Empty →
BinarySearchTree res ∧
(∀ x, minValue tree x ∧ x < value → minValue res x) ∧
(∀ x, maxValue tree x ∧ x > value → maxValue res x) := sorry

/-- Insert value into binary search tree -/
def insert (tree : Tree) (value : Int) : Tree := sorry

/-- Specification for insertion -/
theorem insert_spec (tree : Tree) (value : Int) :
BinarySearchTree tree →
BinarySearchTree (insert tree value) := sorry
