-- <vc-preamble>
def BinaryIndexedTree : Type := Unit
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def BinaryIndexedTree.mk (n : Nat) : BinaryIndexedTree :=
sorry

def BinaryIndexedTree.add (self : BinaryIndexedTree) (i : Nat) (x : Int) : Unit :=
sorry

def BinaryIndexedTree.sum (self : BinaryIndexedTree) (i : Nat) : Int :=
sorry

def BinaryIndexedTree.sum_range (self : BinaryIndexedTree) (l r : Nat) : Int :=
sorry

def BinaryIndexedTree.data (self : BinaryIndexedTree) : List Int :=
sorry

def solve (n : Nat) (perm : List Nat) : List Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem bit_init_properties (n : Nat) (h : n > 0) :
  let bit := BinaryIndexedTree.mk n
  List.length (BinaryIndexedTree.data bit) = n + 1 ∧
  List.all (BinaryIndexedTree.data bit) (λ x => x = 0) :=
sorry

theorem bit_add_sum_properties (n i : Nat) (x : Int) (h1 : n > 0) (h2 : i > 0) (h3 : i ≤ n) :
  let bit := BinaryIndexedTree.mk n
  let bit' := BinaryIndexedTree.add bit i x
  BinaryIndexedTree.sum bit i = x ∧ BinaryIndexedTree.sum bit n = x :=
sorry

theorem bit_range_sum_property (n l r : Nat) (h1 : n > 0) (h2 : l > 0) (h3 : r > 0)
  (h4 : l ≤ r) (h5 : r ≤ n) :
  let bit := BinaryIndexedTree.mk n
  let bit' := List.foldl (λ b i => BinaryIndexedTree.add b (i + l) 1) bit (List.range (r - l + 1))
  BinaryIndexedTree.sum_range bit' l r = r - l + 1 :=
sorry

theorem solve_properties (n : Nat) (perm : List Nat) (h1 : n > 0)
  (h2 : List.length perm = n)
  (h3 : ∀ i j, i < j → perm.get! i < perm.get! j)
  (h4 : List.Nodup perm) :
  let result := solve n perm
  List.length result = n ∧
  List.all result (λ x => x ≥ 0) ∧
  result.head? = some 0 :=
sorry
-- </vc-theorems>