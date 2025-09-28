use vstd::prelude::*;

verus! {

spec fn sorted(q: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i <= j < q.len() ==> q[i] <= q[j]
}


// all the values in the range satisfy `comparer` (comparer(q[i], key) == true)
spec fn range_satisfies_comparer(q: Seq<int>, key: int, lower_bound: nat, upper_bound: nat, comparer: spec_fn(int, int) -> bool) -> bool
    recommends 0 <= lower_bound <= upper_bound <= q.len()
{
    forall|i: int| lower_bound <= i < upper_bound ==> comparer(q[i], key)
}

// all the values in the range satisfy `!comparer` (comparer(q[i], key) == false)
spec fn range_satisfies_comparer_negation(q: Seq<int>, key: int, lower_bound: nat, upper_bound: nat, comparer: spec_fn(int, int) -> bool) -> bool
    recommends 0 <= lower_bound <= upper_bound <= q.len()
{
    range_satisfies_comparer(q, key, lower_bound, upper_bound, |n1, n2| !comparer(n1, n2))
}

// <vc-helpers>
spec fn is_strictly_greater(n1: int, n2: int) -> bool {
    n1 > n2
}

spec fn is_greater_than_or_equal(n1: int, n2: int) -> bool {
    n1 >= n2
}

proof fn lemma_comparer_property(comparer: spec_fn(int, int) -> bool, n1: int, n2: int)
    requires
        (forall|a: int, b: int| #[trigger] comparer(a, b) ==> comparer(a, b) == (a > b)) ||
        (forall|a: int, b: int| #[trigger] comparer(a, b) ==> comparer(a, b) == (a >= b)),
    ensures
        (comparer(n1, n2) == is_strictly_greater(n1, n2)) || (comparer(n1, n2) == is_greater_than_or_equal(n1, n2))
{
    if (forall|a: int, b: int| #[trigger] comparer(a, b) ==> comparer(a, b) == (a > b)) {
        assert(comparer(n1, n2) == (n1 > n2));
    } else {
        assert(forall|a: int, b: int| #[trigger] comparer(a, b) ==> comparer(a, b) == (a >= b));
        assert(comparer(n1, n2) == (n1 >= n2));
    }
}

proof fn lemma_range_satisfies_comparer_split(
    q: Seq<int>, key: int, start: nat, mid: nat, end: nat,
    comparer: spec_fn(int, int) -> bool
)
    requires
        0 <= start <= mid <= end <= q.len(),
        range_satisfies_comparer(q, key, start, mid, comparer),
        range_satisfies_comparer(q, key, mid, end, comparer),
    ensures
        range_satisfies_comparer(q, key, start, end, comparer),
{
    assert forall|i: int| start <= i < end implies comparer(q[i], key) by {
        if start <= i < mid {
            assert(range_satisfies_comparer(q, key, start, mid, comparer));
            assert(comparer(q[i], key));
        } else if mid <= i < end {
            assert(range_satisfies_comparer(q, key, mid, end, comparer));
            assert(comparer(q[i], key));
        }
    }
}

proof fn lemma_range_satisfies_comparer_negation_split(
    q: Seq<int>, key: int, start: nat, mid: nat, end: nat,
    comparer: spec_fn(int, int) -> bool
)
    requires
        0 <= start <= mid <= end <= q.len(),
        range_satisfies_comparer_negation(q, key, start, mid, comparer),
        range_satisfies_comparer_negation(q, key, mid, end, comparer),
    ensures
        range_satisfies_comparer_negation(q, key, start, end, comparer),
{
    assert forall|i: int| start <= i < end implies !comparer(q[i], key) by {
        if start <= i < mid {
            assert(range_satisfies_comparer_negation(q, key, start, mid, comparer));
            assert(!comparer(q[i], key));
        } else if mid <= i < end {
            assert(range_satisfies_comparer_negation(q, key, mid, end, comparer));
            assert(!comparer(q[i], key));
        }
    }
}

proof fn lemma_sorted_range(q: Seq<int>, i: int, j: int, k: int)
    requires
        sorted(q),
        0 <= i <= j <= k < q.len(),
    ensures
        q[i] <= q[j] <= q[k]
{
    assert(q[i] <= q[j]);
    assert(q[j] <= q[k]);
}

proof fn lemma_monotonicity_condition_on_comparer(q: Seq<int>, key: int, i: int, j: int, comparer: spec_fn(int, int) -> bool)
    requires
        sorted(q),
        (forall|n1: int, n2: int| #[trigger] comparer(n1, n2) ==> comparer(n1, n2) == (n1 > n2)) ||
        (forall|n1: int, n2: int| #[trigger] comparer(n1, n2) ==> comparer(n1, n2) == (n1 >= n2)),
        0 <= i <= j < q.len(), // Changed from i < j
    ensures
        !comparer(q[j], key) ==> !comparer(q[i], key),
        comparer(q[i], key) ==> comparer(q[j], key),
{
    lemma_comparer_property(comparer, q[i], key);
    lemma_comparer_property(comparer, q[j], key);

    assert(q[i] <= q[j]); // From sorted(q) and i <= j

    if comparer(q[i], key) == (q[i] > key) { // Comparer is strictly greater
        assert(comparer(q[j], key) == (q[j] > key));
        if !comparer(q[j], key) { // q[j] <= key
            assert(q[i] <= q[j] <= key);
            assert(!comparer(q[i], key)); // q[i] <= key
        }
        if comparer(q[i], key) { // q[i] > key
            assert(q[j] >= q[i] > key);
            assert(comparer(q[j], key)); // q[j] > key
        }
    } else { // Comparer is greater than or equal
        assert(comparer(q[i], key) == (q[i] >= key));
        assert(comparer(q[j], key) == (q[j] >= key));
        if !comparer(q[j], key) { // q[j] < key
            assert(q[i] <= q[j] < key);
            assert(!comparer(q[i], key)); // q[i] < key
        }
        if comparer(q[i], key) { // q[i] >= key
            assert(q[j] >= q[i] >= key);
            assert(comparer(q[j], key)); // q[j] >= key
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn binary_search(q: Seq<int>, key: int, lower_bound: usize, upper_bound: usize, comparer: spec_fn(int, int) -> bool) -> (index: usize)
    requires
        sorted(q),
        0 <= lower_bound <= upper_bound <= q.len(),
        range_satisfies_comparer_negation(q, key, lower_bound as nat, upper_bound as nat, comparer),
        range_satisfies_comparer(q, key, upper_bound as nat, q.len() as nat, comparer),
        // comparer is '>' or '>='
        (forall|n1: int, n2: int| #[trigger] comparer(n1, n2) ==> comparer(n1, n2) == (n1 > n2)) ||
        (forall|n1: int, n2: int| #[trigger] comparer(n1, n2) ==> comparer(n1, n2) == (n1 >= n2)),

    ensures
        lower_bound <= index <= upper_bound,
        range_satisfies_comparer_negation(q, key, 0nat, index as nat, comparer),
        range_satisfies_comparer(q, key, index as nat, q.len() as nat, comparer),
// </vc-spec>
// <vc-code>
{
    let mut low: usize = lower_bound;
    let mut high: usize = upper_bound;

    while low < high {
        invariant!(
            low <= high,
            lower_bound <= low,
            high <= upper_bound,
            range_satisfies_comparer_negation(q, key, 0nat, low as nat, comparer),
            range_satisfies_comparer(q, key, high as nat, q.len() as nat, comparer),
            q.len() == old(q.len()),
            lower_bound == old(lower_bound),
            upper_bound == old(upper_bound),
            comparer == old(comparer),
            key == old(key),
            sorted(q),
            (forall|n1: int, n2: int| #[trigger] comparer(n1, n2) ==> comparer(n1, n2) == (n1 > n2)) ||
            (forall|n1: int, n2: int| #[trigger] comparer(n1, n2) ==> comparer(n1, n2) == (n1 >= n2)),
        );
        decreases((high - low) as int);

        let mid = low + (high - low) / 2;
        assert(low <= mid);
        if high - low == 1 {
            assert(mid == low);
            assert(mid < high);
        } else if high - low > 1 {
            assert(mid < high);
        }

        if comparer(q.tracked_data()[mid as int], key) {
            // q[mid] satisfies comparer. Since q is sorted, all elements after mid where monotonicity holds will also satisfy comparer.
            // Also, elements in [high, q.len()) already satisfy comparer from invariant.
            // Thus, elements in [mid, q.len()) satisfy comparer.
            high = mid;

            proof {
                assert forall |k: int| high as int <= k < old(high) implies comparer(q[k], key) by {
                    lemma_monotonicity_condition_on_comparer(q, key, high as int, k, comparer);
                }
                lemma_range_satisfies_comparer_split(q, key, high as nat, old(high) as nat, q.len() as nat, comparer);
                assert(range_satisfies_comparer(q, key, high as nat, q.len() as nat, comparer));

            }
        } else {
            // !comparer(q[mid], key). Since q is sorted, all elements before mid where monotonicity holds will also not satisfy comparer.
            // Also, elements in [0, low) already do not satisfy comparer from invariant.
            // Thus, elements in [0, mid+1) do not satisfy comparer.
            low = mid + 1;

            proof {
                assert forall |k: int| old(low) as int <= k < low as int implies !comparer(q[k], key) by {
                    lemma_monotonicity_condition_on_comparer(q, key, k, (low -1) as int, comparer);
                }
                lemma_range_satisfies_comparer_negation_split(q, key, 0nat, old(low) as nat, low as nat, comparer);
                assert(range_satisfies_comparer_negation(q, key, 0nat, low as nat, comparer));
            }
        }
    }

    proof {
        assert(low == high);
        // Prove post-conditions
        assert(lower_bound <= low);
        assert(low <= upper_bound);

        // Final assertion: range_satisfies_comparer_negation(q, key, 0nat, low as nat, comparer)
        assert(range_satisfies_comparer_negation(q, key, 0nat, low as nat, comparer));

        // Final assertion: range_satisfies_comparer(q, key, low as nat, q.len() as nat, comparer)
        assert(range_satisfies_comparer(q, key, low as nat, q.len() as nat, comparer));
    }
    low
}
// </vc-code>

fn main() {
}

}