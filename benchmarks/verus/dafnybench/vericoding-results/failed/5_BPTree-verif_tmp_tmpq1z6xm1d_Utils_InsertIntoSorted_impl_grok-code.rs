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
fn get_insert_index(a: &[int], limit: usize, x: int) -> (idx: usize)
    requires 
        !a@.contains(x),
        limit <= a.len(),
        sorted_seq(a@.take(limit as int)),
    ensures
        idx <= limit,
        sorted_seq(a@.take(limit as int)),
        idx > 0 ==> a@[(idx as int) - 1] < x,
        idx < limit ==> x < a@[idx as int],
{
    if limit == 0{
        return 0;
    }
    let mut low: usize = 0;
    let mut high: usize = limit;
    while low < high
        invariant
            0 <= low <= high <= limit,
            sorted_seq(a@.take(limit as int)),
            !a@.contains(x),
            forall|i: int| 0 <= i < low ==> a@[i] < x,
            forall|i: int| high <= i < limit ==> a@[i] > x,
    {
        let mid = low + (high - low) / 2;
        if a@[mid as int] < x {
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
    let insert_idx: usize = get_insert_index(a, limit, key);
    proof {
        assert(forall|i: int| #[trigger] 0 <= i < limit ==> a@[i] > 0);
        assert(key > 0);
        assert(!a@.contains(key));
        assert(sorted(a@.take(limit as int)));
        assert(insert_idx <= limit);
        assert(insert_idx == 0 || (insert_idx > 0 && a@[(insert_idx as int) - 1] < key));
        assert(insert_idx == limit || (insert_idx < limit && key < a@[insert_idx as int]));
    }
    let mut b: Vec<int> = Vec::with_capacity(a.len());
    let mut i: usize = 0;
    while i < insert_idx 
        invariant
            0 <= i <= insert_idx,
            b.len() == i,
            forall|j: int| 0 <= j < b.len() ==> b@[j] == a@[j],
            forall|j: int| 0 <= j < b.len() ==> b@[j] < key,
            forall|j: int| 0 <= j < b.len() ==> b@[j] > 0,
    {
        b.push(a@[i as int]);
        proof {
            assert(b@[b.len() - 1] > 0);
            assert(b@[b.len() - 1] < key);
        }
        i = i + 1;
    }
    b.push(key);
    proof {
        assert(b@[insert_idx as int] == key);
        assert(sorted(b@.take((i as int) + 1)));
    }
    i = insert_idx;
    while i < limit 
        invariant
            insert_idx <= i <= limit,
            b.len() == insert_idx + 1 + (i - insert_idx),
            forall|j: int| 0 <= j < insert_idx ==> b@[j] == a@[j],
            b@[insert_idx as int] == key,
            forall|j: int| 0 <= j < insert_idx ==> b@[j] < key,
            forall|j: int| insert_idx + 1 <= j < b.len() ==> b@[j] == a@[j - 1],
            forall|j: int| insert_idx + 1 <= j < b.len() ==> key < b@[j],
            forall|j: int| insert_idx + 1 <= j < b.len() ==> b@[j] > 0,
            sorted(b@.take(b.len() as int)),
    {
        b.push(a@[i as int]);
        proof {
            assert(key < b@[b.len() - 1]);
            assert(b@[b.len() - 1] > 0);
            assert(sorted(b@.take(b.len() as int)));
        }
        i = i + 1;
    }
    while b.len() < a.len()
        invariant
            limit <= b.len() <= a.len(),
            forall|j: int| b.len() <= j < a.len() ==> a@[j] == 0,
            sorted(b@.take((limit + 1) as int)),
            forall|j: int| 0 <= j < limit + 1 ==> b@[j] > 0,
            forall|j: int| 0 <= j < limit ==> a@.contains(b@[j]),
            forall|j: int| b.len() <= j < a.len() ==> 0 == 0,
    {
        b.push(0);
        proof {
            assert(b@[b.len() - 1] == 0);
        }
    }
    proof {
        assert(sorted(b@.take((limit + 1) as int)));
        assert(forall|i: int| #[trigger] 0 <= i < limit + 1 ==> b@[i] > 0);
        assert(forall|i: int| #[trigger] 0 <= i < limit ==> a@.contains(b@[i]));
        assert(forall|i: int| #[trigger] limit + 1 <= i < b.len() ==> b@[i] == 0);
        assert(b.len() == a.len());
    }
    b
}
// </vc-code>

fn main() {}

}