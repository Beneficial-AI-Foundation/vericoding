-- <vc-preamble>
def HashMap := List

structure RandomizedCollection where
  idx : List (Int × List Nat)
  val : List Int
deriving Repr

def find? (l : List (Int × List Nat)) (k : Int) : Option (List Nat) :=
  (l.find? (fun p => p.1 = k)).map (·.2)

def sum (xs : List Nat) : Nat :=
  match xs with
  | [] => 0
  | x :: rest => x + sum rest
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def RandomizedCollection.getRandom : RandomizedCollection → Int := sorry

def RandomizedCollection.insert : RandomizedCollection → Int → Bool :=
sorry

def RandomizedCollection.remove : RandomizedCollection → Int → Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem insert_property (rc : RandomizedCollection) (v : Int) :
  let inserted := RandomizedCollection.insert rc v
  (find? rc.idx v).isSome → inserted = false ∧
  (find? rc.idx v).isNone → inserted = true :=
sorry

theorem remove_property (rc : RandomizedCollection) (v : Int) :
  let removed := RandomizedCollection.remove rc v
  (find? rc.idx v).isSome → removed = true ∧
  (find? rc.idx v).isNone → removed = false :=
sorry

theorem getRandom_property (rc : RandomizedCollection) :
  rc.val.length > 0 →
  let randVal := RandomizedCollection.getRandom rc
  (find? rc.idx randVal).isSome :=
sorry

theorem internal_consistency (rc : RandomizedCollection) :
  rc.val.length = sum (rc.idx.map (·.2.length)) ∧
  (∀ pair ∈ rc.idx, ∀ idx ∈ pair.2, idx < rc.val.length) :=
sorry

theorem indices_point_to_values (rc : RandomizedCollection) :
  ∀ v indices, find? rc.idx v = some indices →
  ∀ idx ∈ indices, rc.val.get? idx = some v :=
sorry

theorem random_distribution (rc : RandomizedCollection) (samples : List Int)
  (h : ∀ s ∈ samples, s = RandomizedCollection.getRandom rc) :
  (∀ s ∈ samples, (find? rc.idx s).isSome) ∧
  ∃ subset : List Int, subset ≠ [] ∧ ∀ x ∈ subset, x ∈ rc.val :=
sorry
-- </vc-theorems>