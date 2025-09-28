use vstd::prelude::*;

verus! {

// Function SetLessThan equivalent
spec fn set_less_than(numbers: Set<int>, threshold: int) -> Set<int> {
    numbers.filter(|i: int| i < threshold)
}

// Function seqSet equivalent
spec fn seq_set(nums: Seq<int>, index: nat) -> Set<int> {
    if index < nums.len() {
        Set::new(|x: int| exists|i: int| 0 <= i < index && i < nums.len() && nums[i] == x)
    } else {
        Set::empty()
    }
}

// Predicate SortedSeq equivalent
spec fn sorted_seq(a: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i < j < a.len() ==> a[i] < a[j]
}

// Method GetInsertIndex equivalent
fn get_insert_index(a: &[int], limit: usize, x: int) -> (idx: usize)
    requires 
        !a@.contains(x),
        limit <= a.len(),
        sorted_seq(a@.take(limit as int)),
    ensures
        idx <= limit,
        sorted_seq(a@.take(limit as int)),
        idx > 0 ==> a[(idx - 1) as int] < x,
        idx < limit ==> x < a[idx as int],
{
    assume(false);
    0
}

// Predicate sorted equivalent
spec fn sorted(a: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i < j < a.len() ==> a[i] < a[j]
}

// Predicate distinct equivalent
spec fn distinct(a: Seq<int>) -> bool {
    forall|i: int, j: int| (0 <= i < a.len() && 0 <= j < a.len() && i != j) ==> a[i] != a[j]
}

// Predicate sorted_eq equivalent
spec fn sorted_eq(a: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i < j < a.len() ==> a[i] <= a[j]
}

// Predicate lessThan equivalent
spec fn less_than(a: Seq<int>, key: int) -> bool {
    forall|i: int| 0 <= i < a.len() ==> a[i] < key
}

// Predicate greaterThan equivalent
spec fn greater_than(a: Seq<int>, key: int) -> bool {
    forall|i: int| 0 <= i < a.len() ==> a[i] > key
}

// Predicate greaterEqualThan equivalent
spec fn greater_equal_than(a: Seq<int>, key: int) -> bool {
    forall|i: int| 0 <= i < a.len() ==> a[i] >= key
}

// Function count equivalent
spec fn count(a: Seq<bool>) -> nat
    decreases a.len()
{
    if a.len() == 0 { 
        0nat 
    } else { 
        (if a[0] { 1nat } else { 0nat }) + count(a.drop_first())
    }
}

// <vc-helpers>
// Helper lemma to prove that taking elements preserves sortedness
proof fn sorted_take_preserves(a: Seq<int>, n: int, m: int)
    requires
        0 <= n <= m <= a.len(),
        sorted(a.take(m)),
    ensures
        sorted(a.take(n)),
{
    assert forall|i: int, j: int| 0 <= i < j < n implies a[i] < a[j] by {
        assert(i < m);
        assert(j < m);
        assert(a.take(m)[i] == a[i]);
        assert(a.take(m)[j] == a[j]);
    }
}

// Helper to prove sorted after insertion
proof fn sorted_after_insert(a: Seq<int>, idx: int, key: int)
    requires
        0 <= idx <= a.len(),
        sorted(a),
        idx > 0 ==> a[idx - 1] < key,
        idx < a.len() ==> key < a[idx],
    ensures
        sorted(a.take(idx).push(key) + a.skip(idx)),
{
    let result = a.take(idx).push(key) + a.skip(idx);
    assert forall|i: int, j: int| 0 <= i < j < result.len() implies result[i] < result[j] by {
        if i < idx && j == idx {
            assert(result[i] == a[i]);
            assert(result[j] == key);
            if idx > 0 && i == idx - 1 {
                assert(a[idx - 1] < key);
            } else {
                assert(a[i] < a[idx - 1] < key);
            }
        } else if i < idx && j > idx {
            assert(result[i] == a[i]);
            assert(result[j] == a[j - 1]);
            assert(a[i] < a[idx] <= a[j - 1]);
        } else if i == idx && j > idx {
            assert(result[i] == key);
            assert(result[j] == a[j - 1]);
            assert(key < a[idx] <= a[j - 1]);
        } else if i < idx && j < idx {
            assert(result[i] == a[i]);
            assert(result[j] == a[j]);
        } else if i > idx && j > idx {
            assert(result[i] == a[i - 1]);
            assert(result[j] == a[j - 1]);
            assert(a[i - 1] < a[j - 1]);
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn insert_into_sorted(a: &[int], limit: usize, key: int) -> (b: Vec<int>)
    requires 
        key > 0,
        !a@.contains(key),
        limit < a.len(),
        forall|i: int| 0 <= i < limit ==> a[i] > 0,
        forall|i: int| limit <= i < a.len() ==> a[i] == 0,
        sorted(a@.take(limit as int)),
    ensures
        b.len() == a.len(),
        sorted(b@.take((limit + 1) as int)),
        forall|i: int| limit + 1 <= i < b.len() ==> b[i] == 0,
        forall|i: int| 0 <= i < limit ==> a@.contains(b[i]),
        forall|i: int| 0 <= i < limit + 1 ==> b[i] > 0,
// </vc-spec>
// <vc-code>
{
    let idx = get_insert_index(a, limit, key);
    
    let mut b: Vec<int> = Vec::with_capacity(a.len());
    
    // Add elements before insertion point
    let mut i = 0;
    while i < idx
        invariant
            i <= idx,
            idx <= limit,
            b@.len() == i,
            forall|j: int| 0 <= j < i ==> b@[j] == a[j],
            forall|j: int| 0 <= j < i ==> b@[j] > 0,
    {
        b.push(a[i as usize]);
        i += 1;
    }
    
    // Insert the key
    b.push(key);
    assert(b@.len() == idx + 1);
    
    // Add remaining elements from the sorted portion
    while i < limit
        invariant
            idx <= i <= limit,
            b@.len() == i + 1,
            forall|j: int| 0 <= j < idx ==> b@[j] == a[j],
            b@[idx as int] == key,
            forall|j: int| idx < j < i + 1 ==> b@[j] == a[j - 1],
            forall|j: int| 0 <= j < i + 1 ==> b@[j] > 0,
    {
        b.push(a[i as usize]);
        i += 1;
    }
    
    assert(b@.len() == limit + 1);
    
    // Add zeros from the rest of the array
    while i < a.len()
        invariant
            limit <= i <= a.len(),
            b@.len() == i + 1,
            forall|j: int| 0 <= j < idx ==> b@[j] == a[j],
            b@[idx as int] == key,
            forall|j: int| idx < j < limit + 1 ==> b@[j] == a[j - 1],
            forall|j: int| limit + 1 <= j < i + 1 ==> b@[j] == 0,
            forall|j: int| 0 <= j < limit + 1 ==> b@[j] > 0,
    {
        b.push(0int);
        i += 1;
    }
    
    // Prove sortedness of the result
    proof {
        assert(b@.len() == a.len());
        
        // Prove sorted for first limit+1 elements
        assert forall|i: int, j: int| 0 <= i < j < limit + 1 implies b@[i] < b@[j] by {
            if i < idx && j == idx {
                assert(b@[i] == a[i]);
                assert(b@[j] == key);
                if i == idx - 1 {
                    assert(a[i] < key);
                } else {
                    assert(a[i] < a[idx - 1] < key);
                }
            } else if i < idx && j > idx {
                assert(b@[i] == a[i]);
                assert(b@[j] == a[j - 1]);
                if idx < limit {
                    assert(a[i] < a[idx as int] <= a[j - 1]);
                } else {
                    assert(a[i] < key);
                    assert(key < a[j - 1]);
                }
            } else if i == idx && j > idx {
                assert(b@[i] == key);
                assert(b@[j] == a[j - 1]);
                assert(key < a[idx as int] <= a[j - 1]);
            } else if i < idx && j < idx {
                assert(b@[i] == a[i]);
                assert(b@[j] == a[j]);
                assert(a[i] < a[j]);
            } else if i > idx && j > idx {
                assert(b@[i] == a[i - 1]);
                assert(b@[j] == a[j - 1]);
                assert(a[i - 1] < a[j - 1]);
            }
        }
        
        assert(sorted(b@.take((limit + 1) as int)));
        
        // Prove elements in sorted portion come from original array (except key)
        assert forall|i: int| 0 <= i < limit implies a@.contains(b@[i]) by {
            if i < idx {
                assert(b@[i] == a[i]);
            } else {
                assert(b@[i + 1] == a[i]);
            }
        }
    }
    
    b
}
// </vc-code>

fn main() {}

}