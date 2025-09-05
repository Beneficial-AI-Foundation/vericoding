Design a data structure that supports all following operations in average O(1) time.
Note: Duplicate elements are allowed.

insert(val): Inserts an item val to the collection.
remove(val): Removes an item val from the collection if present.
getRandom: Returns a random element from current collection of elements. The probability of each element being returned is linearly related to the number of same value the collection contains.

Example:

// Init an empty collection.
RandomizedCollection collection = new RandomizedCollection();

// Inserts 1 to the collection. Returns true as the collection did not contain 1.
collection.insert(1);

// Inserts another 1 to the collection. Returns false as the collection contained 1. Collection now contains [1,1].
collection.insert(1);

// Inserts 2 to the collection, returns true. Collection now contains [1,1,2].
collection.insert(2);

// getRandom should return 1 with the probability 2/3, and returns 2 with the probability 1/3.
collection.getRandom();

// Removes 1 from the collection, returns true. Collection now contains [1,2].
collection.remove(1);

// getRandom should return 1 and 2 both equally likely.
collection.getRandom();

def HashMap := List

structure RandomizedCollection where
  idx : List (Int × List Nat)  
  val : List Int
deriving Repr

def RandomizedCollection.insert : RandomizedCollection → Int → Bool := sorry
def RandomizedCollection.remove : RandomizedCollection → Int → Bool := sorry 

def RandomizedCollection.getRandom : RandomizedCollection → Int := sorry

def find? (l : List (Int × List Nat)) (k : Int) : Option (List Nat) :=
  (l.find? (fun p => p.1 = k)).map (·.2)

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded