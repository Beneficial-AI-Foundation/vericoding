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
fn get_insert_index(a: &[i32], limit: usize, x: i32) -> (idx: usize)
    requires
        !a@.contains(x),
        limit <= a.len(),
        sorted_seq(a@.take(limit as int)),
    ensures
        idx <= limit,
        idx > 0 ==> a[(idx - 1) as int] < x,
        idx < limit ==> x < a[idx as int],
{
    let mut low: usize = 0;
    let mut high: usize = limit;

    while low < high
        invariant
            low <= high,
            high <= limit,
            low <= limit,
            sorted_seq(a@.take(limit as int)),
            forall |i: int| 0 <= i < low ==> a[i as int] < x,
            forall |i: int| high <= i < limit ==> x < a[i as int],
    {
        let mid: usize = low + (high - low) / 2;
        if a[mid as int] < x {
            low = mid + 1;
        } else {
            high = mid;
        }
    }
    low
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
    let mut b: Vec<i32> = Vec::new();
    b.reserve(a.len());

    let idx = get_insert_index(a, limit, key);

    let mut i: usize = 0;
    while i < idx
        invariant
            0 <= i <= idx,
            b.len() == i,
            b@.len() == i,
            forall|j: int| 0 <= j < i ==> a[j] == b[j],
            forall|k: int| 0 <= k < i ==> b[k] > 0,
            sorted(b@.take(i as int)),
            limit < a.len(),
            forall|j: int| 0 <= j < limit ==> a[j] > 0,
            forall|j: int| limit <= j < a.len() ==> a[j] == 0,
            idx <= limit,
            sorted(a@.take(limit as int)),
    {
        b.push(a[i]);
        i += 1;
    }

    if idx == i {
        b.push(key);
    }

    let mut k: usize = idx;
    while k < limit
        invariant
            idx <= k <= limit,
            b.len() == idx + (k - idx) + (if idx == i { 1 } else { 0 }),
            b@.len() == idx + (k - idx) + (if idx == i { 1 } else { 0 }),
            if idx == i {
                forall|j: int| 0 <= j < idx ==> a[j] == b[j]
            } else { true },
            if idx == i {
                b[idx as int] == key
            } else { true },
            if idx == i { // When key is inserted, all elements up to current len are positive
                forall|j: int| 0 <= j < idx + (k - idx) + 1 ==> b[j] > 0
            } else { // When key is not inserted, all elements up to current len are positive
                forall|j: int| 0 <= j < idx + (k - idx) ==> b[j] > 0
            },
            sorted(b@.take((idx + (k - idx) + (if idx == i { 1 } else { 0 })) as int)),
            limit < a.len(),
            forall|j: int| 0 <= j < limit ==> a[j] > 0,
            forall|j: int| limit <= j < a.len() ==> a[j] == 0,
            idx <= limit,
            sorted(a@.take(limit as int)),
            forall |j: int| (idx as int) <= j < k ==> b[j + (if idx == i {1} else {0})] == a[j], // Fix here: adjust index for b after insertion
    {
        b.push(a[k]);
        k += 1;
    }

    while b.len() < a.len()
        invariant
            b.len() <= a.len(),
            a.len() == b.capacity(),
            limit < a.len(),
            forall|j: int| 0 <= j < limit ==> a[j] > 0,
            forall|j: int| limit <= j < a.len() ==> a[j] == 0,
            idx <= limit,
            sorted(a@.take(limit as int)),
            ({
                let current_b_len_val = b.len();
                let b_seq = b@;
                let mut valid_part_len: int = 0;
                if idx == i { // key has been inserted
                    valid_part_len = current_b_len_val as int;
                    && sorted(b_seq.take(valid_part_len))
                    && forall|x: int| 0 <= x < idx  ==> b_seq[x] == a[x]
                    && b_seq[idx as int] == key
                    && forall|x: int| (idx +1) <= x < current_b_len_val ==> b_seq[x] == a[x-1]
                } else { // key not yet inserted, or insertion point is at the very end
                    valid_part_len = current_b_len_val as int;
                    && sorted(b_seq.take(valid_part_len))
                    && forall|x: int| 0 <= x < current_b_len_val ==> b_seq[x] == a[x]
                }
            }),
            b.len() > 0 ==> b@.take(b.len() as int).map_values(|e: int| e > 0).fold(true, |acc, x| acc && x),
    {
        b.push(0);
    }

    assert(b.len() == a.len());

    proof {
        assert forall|i: int| 0 <= i < limit + 1 implies b[i] > 0 by {
            if i < idx {
                assert(b[i] == a[i]);
                assert(a[i] > 0);
            } else if i == idx {
                assert(b[i] == key);
                assert(key > 0);
            } else { // i > idx && i < limit + 1
                assert(b[i] == a[i-1]);
                assert(i -1 < limit);
                assert(a[i-1] > 0);
            }
        };

        if idx > 0 {
            assert(a[(idx - 1) as int] < key); // From get_insert_index
        }
        if idx < limit {
            assert(key < a[idx as int]); // From get_insert_index
        }

        assert forall|i: int, j: int| 0 <= i < j < limit + 1 implies b[i] < b[j] by {
            if i < idx && j < idx {
                assert(a[i] < a[j]);
                assert(b[i] == a[i]);
                assert(b[j] == a[j]);
            } else if i < idx && j == idx {
                assert(b[i] == a[i]);
                assert(b[j] == key);
                assert(a[i] < key); // From get_insert_index and sorted(a@.take(limit as int))
            } else if i < idx && j > idx && j < limit + 1 {
                assert(b[i] == a[i]);
                assert(b[j] == a[j-1]);
                assert(a[i] < key); // From get_insert_index
                assert(key < a[j-1]); // From get_insert_index
                assert(a[i] < a[j-1]);
            } else if i == idx && j > idx && j < limit + 1 {
                assert(b[i] == key);
                assert(b[j] == a[j-1]);
                assert(key < a[j-1]); // From get_insert_index
            } else if i > idx && j > idx && j < limit + 1 {
                assert(b[i] == a[i-1]);
                assert(b[j] == a[j-1]);
                assert(i-1 < j-1);
                assert(a[i-1] < a[j-1]); // From sorted(a@.take(limit as int))
            }
        };

        assert(sorted(b@.take((limit + 1) as int)));

        let current_filled_len: int = idx as int + (if idx == i { 1 } else { 0 }) + ((k - idx) as int); // Using variable 'k' from second loop
        assert forall|i: int| limit + 1 <= i < b.len() implies b[i] == 0 by {
            assert(b.len() == a.len());
            assert(limit < a.len());
            if i >= current_filled_len {
                assert(b[i] == 0);
            }
        };

        assert forall|i: int| 0 <= i < limit implies a@.contains(b[i]) by {
           if i < idx {
               assert(b[i] == a[i]);
               assert(a@.contains(a[i]));
            } else { // i > idx
               assert(b[i] == a[i-1]);
               assert(a@.contains(a[i-1]));
            }
        };
    }
    b
}
// </vc-code>

fn main() {}

}