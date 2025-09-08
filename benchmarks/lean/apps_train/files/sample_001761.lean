/-
Design a data structure that supports all following operations in average O(1) time.

insert(val): Inserts an item val to the set if not already present.
remove(val): Removes an item val from the set if present.
getRandom: Returns a random element from current set of elements. Each element must have the same probability of being returned.

Example:

// Init an empty set.
RandomizedSet randomSet = new RandomizedSet();

// Inserts 1 to the set. Returns true as 1 was inserted successfully.
randomSet.insert(1);

// Returns false as 2 does not exist in the set.
randomSet.remove(2);

// Inserts 2 to the set, returns true. Set now contains [1,2].
randomSet.insert(2);

// getRandom should return either 1 or 2 randomly.
randomSet.getRandom();

// Removes 1 from the set, returns true. Set now contains [2].
randomSet.remove(1);

// 2 was already in the set, so return false.
randomSet.insert(2);

// Since 2 is the only number in the set, getRandom always return 2.
randomSet.getRandom();
-/

def RandomizedSet.insert (rs : RandomizedSet) (x : Int) : Bool :=
  sorry

def RandomizedSet.remove (rs : RandomizedSet) (x : Int) : Bool :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def RandomizedSet.getRandom (rs : RandomizedSet) : Int :=
  sorry

theorem insert_sequence (nums : List Int) (h : List.Nodup nums) :
  let rs := RandomizedSet.mk [] []
  let seen := []
  ∀ x ∈ nums,
    (RandomizedSet.insert rs x) = !(x ∈ seen) ∧ 
    rs.list.length = rs.dict.length ∧
    rs.dict.length = seen.length ∧ 
    (∀ (val : Int) (idx : Fin rs.list.length), 
      (val, idx.val) ∈ rs.dict → rs.list.get idx = some val) :=
  sorry

theorem remove_sequence (nums : List Int) (h1 : List.Nodup nums) (h2 : nums ≠ []) :
  let rs := RandomizedSet.mk nums (List.map (fun x => (x, 0)) nums)
  let current := nums 
  ∀ x ∈ nums,
    (RandomizedSet.remove rs x) = (x ∈ current) ∧
    rs.list.length = rs.dict.length ∧ 
    rs.dict.length = current.length ∧
    (∀ (val : Int) (idx : Fin rs.list.length),
      (val, idx.val) ∈ rs.dict → rs.list.get idx = some val) :=
  sorry

theorem get_random_validity (nums : List Int) (h1 : List.Nodup nums) (h2 : nums ≠ []) :
  let rs := RandomizedSet.mk nums (List.map (fun x => (x, 0)) nums)
  let samples := List.replicate 100 (RandomizedSet.getRandom rs)
  (∀ s, s ∈ samples → s ∈ nums) ∧
  (nums.length > 1 → ∃ x y, x ∈ samples ∧ y ∈ samples ∧ x ≠ y) :=
  sorry

theorem mixed_operations (ops : List (Bool × Int)) :
  let rs := RandomizedSet.mk [] []
  let current := []
  ∀ op ∈ ops, match op with
    | (true, val) => 
      (RandomizedSet.insert rs val) = !(val ∈ current) ∧
      (current ≠ [] → RandomizedSet.getRandom rs ∈ current)
    | (false, val) =>
      (RandomizedSet.remove rs val) = (val ∈ current) ∧
      (current ≠ [] → RandomizedSet.getRandom rs ∈ current) :=
  sorry

-- Apps difficulty: interview
-- Assurance level: unguarded