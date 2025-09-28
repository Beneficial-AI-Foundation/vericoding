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
proof fn sorted_take_prefix(a: Seq<int>, i: int, j: int)
    requires 
        0 <= i <= j <= a.len(),
        sorted(a.take(j))
    ensures
        sorted(a.take(i))
{}

proof fn sorted_take_contains(a: Seq<int>, limit: int, x: int)
    requires
        sorted(a.take(limit)),
        0 <= limit <= a.len(),
        forall|i: int| 0 <= i < limit ==> a.contains(a[i])
    ensures
        forall|i: int| 0 <= i < limit ==> a.take(limit).contains(a[i])
{}

proof fn insert_preserves_sorted(a: Seq<int>, limit: nat, key: int, idx: nat)
    requires
        sorted(a.take(limit as int)),
        idx <= limit,
        idx > 0 ==> a[(idx - 1) as int] < key,
        idx < limit ==> key < a[idx as int],
    ensures
        sorted(a.take(idx as int).push(key).add(a.subrange(idx as int, limit as int)))
{
    let result = a.take(idx as int).push(key).add(a.subrange(idx as int, limit as int));
    assert forall|i: int, j: int| 0 <= i < j < result.len() implies result[i] < result[j] by {
        if j == idx {
            if i < idx {
                assert(result[i] == a[i]);
                if idx > 0 {
                    assert(result[i] < key);
                }
            }
        } else if i == idx {
            if j > idx {
                assert(result[j] == a[(j-1) as int]);
                if idx < limit {
                    assert(key < result[j]);
                }
            }
        } else if i < idx && j < idx {
            assert(result[i] == a[i] && result[j] == a[j]);
        } else if i > idx && j > idx {
            assert(result[i] == a[(i-1) as int] && result[j] == a[(j-1) as int]);
        } else if i < idx && j > idx {
            assert(result[i] == a[i] && result[j] == a[(j-1) as int]);
            if idx > 0 && idx < limit {
                assert(a[i] < a[(idx-1) as int]);
                assert(a[(idx-1) as int] < key);
                assert(key < a[idx as int]);
                assert(a[idx as int] <= a[(j-1) as int]);
            }
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
    
    // Copy elements before insertion point
    let mut i = 0;
    while i < idx
        invariant
            0 <= i <= idx,
            idx <= limit,
            b.len() == i,
            forall|j: int| 0 <= j < i ==> b[j] == a[j],
            forall|j: int| 0 <= j < i ==> b[j] > 0,
            sorted(b@),
    {
        b.push(a[i]);
        i += 1;
    }
    
    // Insert the key
    b.push(key);
    
    // Copy remaining elements from the sorted portion
    while i < limit
        invariant
            idx <= i <= limit,
            b.len() == i + 1,
            b[idx as int] == key,
            forall|j: int| 0 <= j < idx ==> b[j] == a[j],
            forall|j: int| idx < j < b.len() ==> b[j] == a[(j-1) as int],
            forall|j: int| 0 <= j < b.len() ==> b[j] > 0,
            sorted(b@),
    {
        b.push(a[i]);
        i += 1;
    }
    
    // Fill remaining positions with 0
    while i < a.len()
        invariant
            limit <= i <= a.len(),
            b.len() == limit + 1,
            b[idx as int] == key,
            forall|j: int| 0 <= j < idx ==> b[j] == a[j],
            forall|j: int| idx < j < limit + 1 ==> b[j] == a[(j-1) as int],
            forall|j: int| 0 <= j < limit + 1 ==> b[j] > 0,
            sorted(b@.take((limit + 1) as int)),
    {
        b.push(0int);
        i += 1;
    }
    
    proof {
        assert(b.len() == a.len());
        assert(sorted(b@.take((limit + 1) as int)));
        assert(forall|i: int| limit + 1 <= i < b.len() ==> b[i] == 0);
        assert(forall|i: int| 0 <= i < limit ==> a@.contains(b[i]));
        assert(forall|i: int| 0 <= i < limit + 1 ==> b[i] > 0);
    }
    
    b
}
// </vc-code>

fn main() {}

}