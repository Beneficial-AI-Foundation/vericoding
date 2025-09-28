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
proof fn lemma_range_satisfies_composer_split(q: Seq<int>, key: int, lower_bound: nat, upper_bound: nat, mid: nat, comparer: spec_fn(int, int) -> bool)
    requires
        0 <= lower_bound <= mid <= upper_bound <= q.len(),
        range_satisfies_comparer(q, key, lower_bound, upper_bound, comparer),
    ensures
        range_satisfies_comparer(q, key, lower_bound, mid, comparer),
        range_satisfies_comparer(q, key, mid, upper_bound, comparer),
{
    assert(forall|i: int| lower_bound <= i < mid ==> comparer(q[i], key)) by {
        assert forall|i: int| lower_bound <= i < mid implies comparer(q[i], key) by {
            assert(comparer(q[i], key));
        }
    }
    assert(forall|i: int| mid <= i < upper_bound ==> comparer(q[i], key)) by {
        assert forall|i: int| mid <= i < upper_bound implies comparer(q[i], key) by {
            assert(comparer(q[i], key));
        }
    }
}

proof fn lemma_range_satisfies_composition_negation_split(q: Seq<int>, key: int, lower_bound: nat, upper_bound: nat, mid: nat, comparer: spec_fn(int, int) -> bool)
    requires
        0 <= lower_bound <= mid <= upper_bound <= q.len(),
        range_satisfies_comparer_negation(q, key, lower_bound, upper_bound, comparer),
    ensures
        range_satisfies_comparer_negation(q, key, lower_bound, mid, comparer),
        range_satisfies_comparer_negation(q, key, mid, upper_bound, comparer),
{
    assert(forall|i: int| lower_bound <= i < mid ==> !comparer(q[i], key)) by {
        assert forall|i: int| lower_bound <= i < mid implies !comparer(q[i], key) by {
            assert(!comparer(q[i], key));
        }
    }
    assert(forall|i: int| mid <= i < upper_bound ==> !comparer(q[i], key)) by {
        assert forall|i: int| mid <= i < upper_bound implies !comparer(q[i], key) by {
            assert(!comparer(q[i], key));
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
    let mut low = lower_bound;
    let mut high = upper_bound;
    
    while low < high 
        invariant 
            lower_bound <= low <= high <= upper_bound,
            range_satisfies_comparer_negation(q, key, 0nat, low as nat, comparer),
            range_satisfies_comparer(q, key, high as nat, q.len() as nat, comparer),
    {
        let mid = low + (high - low) / 2;
        
        if comparer(q[mid as int], key) {
            high = mid;
        } else {
            proof {
                lemma_range_satisfies_composition_negation_split(q, key, low as nat, high as nat, mid as nat, comparer);
            }
            low = mid + 1;
        }
    }
    
    low
}
// </vc-code>

fn main() {
}

}