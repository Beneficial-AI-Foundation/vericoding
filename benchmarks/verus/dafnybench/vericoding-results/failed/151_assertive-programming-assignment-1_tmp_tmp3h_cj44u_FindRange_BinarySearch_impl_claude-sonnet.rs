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
proof fn lemma_range_satisfies_comparer_extends(q: Seq<int>, key: int, lower1: nat, upper1: nat, lower2: nat, upper2: nat, comparer: spec_fn(int, int) -> bool)
    requires
        0 <= lower1 <= upper1 <= q.len(),
        0 <= lower2 <= upper2 <= q.len(),
        lower1 <= lower2,
        upper1 <= upper2,
        range_satisfies_comparer(q, key, lower2, upper1, comparer),
    ensures
        range_satisfies_comparer(q, key, lower2, upper1, comparer),
{
}

proof fn lemma_range_satisfies_comparer_negation_extends(q: Seq<int>, key: int, lower1: nat, upper1: nat, lower2: nat, upper2: nat, comparer: spec_fn(int, int) -> bool)
    requires
        0 <= lower1 <= upper1 <= q.len(),
        0 <= lower2 <= upper2 <= q.len(),
        lower1 <= lower2,
        upper1 <= upper2,
        range_satisfies_comparer_negation(q, key, lower1, upper1, comparer),
    ensures
        range_satisfies_comparer_negation(q, key, lower1, upper1, comparer),
{
}

proof fn lemma_combine_ranges(q: Seq<int>, key: int, lower: nat, mid: nat, upper: nat, comparer: spec_fn(int, int) -> bool)
    requires
        0 <= lower <= mid <= upper <= q.len(),
        range_satisfies_comparer_negation(q, key, lower, mid, comparer),
        range_satisfies_comparer_negation(q, key, mid, upper, comparer),
    ensures
        range_satisfies_comparer_negation(q, key, lower, upper, comparer),
{
}

proof fn lemma_combine_ranges_pos(q: Seq<int>, key: int, lower: nat, mid: nat, upper: nat, comparer: spec_fn(int, int) -> bool)
    requires
        0 <= lower <= mid <= upper <= q.len(),
        range_satisfies_comparer(q, key, lower, mid, comparer),
        range_satisfies_comparer(q, key, mid, upper, comparer),
    ensures
        range_satisfies_comparer(q, key, lower, upper, comparer),
{
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
    let mut low = lower_bound;
    let mut high = upper_bound;
    
    while low < high
        invariant
            lower_bound <= low <= high <= upper_bound,
            range_satisfies_comparer_negation(q, key, lower_bound as nat, low as nat, comparer),
            range_satisfies_comparer(q, key, high as nat, upper_bound as nat, comparer),
            range_satisfies_comparer_negation(q, key, low as nat, high as nat, comparer),
            range_satisfies_comparer(q, key, upper_bound as nat, q.len() as nat, comparer),
    {
        let mid = low + (high - low) / 2;
        assert(low <= mid < high);
        
        if comparer(q[mid], key) {
            proof {
                lemma_combine_ranges(q, key, low as nat, mid as nat, high as nat, comparer);
            }
            high = mid;
        } else {
            proof {
                lemma_combine_ranges(q, key, low as nat, (mid + 1) as nat, high as nat, comparer);
            }
            low = mid + 1;
        }
    }
    
    proof {
        lemma_combine_ranges(q, key, lower_bound as nat, low as nat, upper_bound as nat, comparer);
        lemma_combine_ranges_pos(q, key, low as nat, upper_bound as nat, q.len() as nat, comparer);
    }
    
    low
}
// </vc-code>

fn main() {
}

}