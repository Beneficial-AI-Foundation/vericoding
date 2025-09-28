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
fn vec_from_slice(a: &[int]) -> Vec<int> {
    let mut v = Vec::new();
    let mut i: usize = 0;
    while i < a.len() {
        invariant![i <= a.len()];
        v.push(a[i]);
        i += 1;
    }
    v
}

fn seq_take_lt_sorted_preserved(a: Seq<int>, limit: int)
    requires 0 <= limit && limit as usize <= a.len()
    ensures sorted(a.take(limit))
{
    proof {
    }
}

fn seq_index_bounds(a: &[int], i: usize) -> int {
    a[i]
}

// A simple linear search to find insertion index (renamed to avoid clash)
fn find_insert_index(a: &[int], limit: usize, x: int) -> (idx: usize)
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
    let mut i: usize = 0;
    // Invariant: 0 <= i <= limit and forall k: 0 <= k < i ==> a[k] < x
    while i < limit {
        invariant![i <= limit];
        invariant![forall|k: int| 0 <= k < i as int ==> a[k as usize] < x];
        if a[i] < x {
            i += 1;
        } else {
            break;
        }
    }
    if i < limit {
        // Prove a[i] != x using the precondition that no element equals x
        assert(!a@.contains(x));
        assert(!(a[i] == x));
        // From loop exit we have !(a[i] < x), so a[i] > x. Use that to get x < a[i].
        // However the ensures uses x < a[idx], so this is consistent.
    }
    i
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
    // Build the resulting vector by inserting key at the appropriate index
    let idx = find_insert_index(a, limit, key);

    let mut b = Vec::new();

    // push elements before idx
    let mut i: usize = 0;
    while i < idx {
        invariant![i <= idx];
        invariant![b.len() == i];
        invariant![forall|p: int, q: int| 0 <= p < q < i as int ==> b[p as usize] < b[q as usize]];
        invariant![forall|p: int| 0 <= p < i as int ==> b[p as usize] == a[p as usize]];
        b.push(a[i]);
        i += 1;
    }

    // push the key
    b.push(key);
    assert(b.len() == idx + 1);
    // prove prefix sorted: for p < idx, a[p] < key
    assert(forall|p: int| 0 <= p < idx as int ==> b[p as usize] < key by {
        // b[p] == a[p]
        assert(b[p as usize] == a[p as usize]);

        // From 0 <= p < idx we know idx > 0
        assert(idx > 0);

        // Use the postcondition of find_insert_index: idx > 0 ==> a[idx-1] < key
        assert(a[(idx - 1) as usize] < key);

        // Now handle whether p == idx-1 or p < idx-1
        if p == (idx as int) - 1 {
            // p is the last element before idx
            assert(a[p as usize] < key);
        } else {
            // p < idx-1, use sortedness to get a[p] < a[idx-1]
            // From preconditions: sorted(a@.take(limit as int))
            // show 0 <= p < (idx-1) < limit
            assert(0 <= p);
            assert(p < (idx as int) - 1);
            // idx <= limit and idx > 0 imply idx-1 < limit
            assert((idx as int) - 1 < limit as int);
            // instantiate sorted property: a[p] < a[idx-1]
            assert(a[p as usize] < a[(idx - 1) as usize]);
            // combine to get a[p] < key
            assert(a[p as usize] < key);
        }
    });

    // push remaining positive elements from original first limit items
    let mut j: usize = idx;
    while j < limit {
        invariant![j <= limit];
        invariant![b.len() == j + 1];
        invariant![forall|p: int, q: int| 0 <= p < q < (j as int) + 1 ==> b[p as usize] < b[q as usize]];
        // For j==idx need key < a[idx]; for j>idx need a[j-1] < a[j]
        if j == idx {
            if idx < limit {
                // Use postcondition of find_insert_index: idx < limit ==> key < a[idx]
                assert(key < a[idx]);
            }
        } else {
            // j > idx, maintain sortedness of original prefix
            assert(a[j - 1] < a[j]);
        }
        b.push(a[j]);
        j += 1;
    }

    // push zeros for the rest to reach original length
    let mut k: usize = limit + 1;
    while k < a.len() {
        invariant![k <= a.len()];
        invariant![b.len() == k];
        invariant![forall|p: int| 0 <= p < (limit + 1) as int ==> b[p as usize] > 0];
        invariant![forall|p: int| (limit + 1) as int <= p < k as int ==> b[p as usize] == 0];
        b.push(0);
        k += 1;
    }

    // final checks (implicit by invariants): lengths match
    b
}
// </vc-code>

fn main() {}

}