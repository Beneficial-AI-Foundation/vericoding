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
spec fn comparer_is_ge(comparer: spec_fn(int, int) -> bool) -> bool {
    forall|n1: int, n2: int| #[trigger] comparer(n1, n2) ==> comparer(n1, n2) == (n1 >= n2)
}

spec fn comparer_is_gt(comparer: spec_fn(int, int) -> bool) -> bool {
    forall|n1: int, n2: int| #[trigger] comparer(n1, n2) ==> comparer(n1, n2) == (n1 > n2)
}

proof fn lemma_comparer_properties(comparer: spec_fn(int, int) -> bool)
    requires
        comparer_is_ge(comparer) || comparer_is_gt(comparer)
    ensures
        comparer_is_ge(comparer) || comparer_is_gt(comparer),
        comparer_is_ge(comparer) ==> forall|n1: int, n2: int| n1 >= n2 ==> comparer(n1, n2),
        comparer_is_gt(comparer) ==> forall|n1: int, n2: int| n1 > n2 ==> comparer(n1, n2),
        comparer_is_ge(comparer) ==> forall|n1: int, n2: int| !(n1 >= n2) ==> !comparer(n1, n2),
        comparer_is_gt(comparer) ==> forall|n1: int, n2: int| !(n1 > n2) ==> !comparer(n1, n2)
{
}

proof fn lemma_transitivity_ge()
    ensures forall|a: int, b: int, c: int| a >= b && b >= c ==> a >= c
{
    assert forall|a: int, b: int, c: int| a >= b && b >= c implies a >= c by {
        assert(a >= c);
    };
}

proof fn lemma_transitivity_gt()
    ensures forall|a: int, b: int, c: int| a > b && b > c ==> a > c
{
    assert forall|a: int, b: int, c: int| a > b && b > c implies a > c by {
        assert(a > c);
    };
}

proof fn lemma_ge_implies_gt_or_eq()
    ensures forall|a: int, b: int| a >= b ==> a > b || a == b
{
    assert forall|a: int, b: int| a >= b implies a > b || a == b by {
        assert(a >= b ==> a > b || a == b);
    };
}

proof fn lemma_sorted_property(q: Seq<int>, i: int, j: int)
    requires
        sorted(q),
        0 <= i <= j < q.len()
    ensures
        q[i] <= q[j]
{
}

proof fn lemma_range_satisfies_comparer_monotonic(q: Seq<int>, key: int, lb1: nat, ub1: nat, lb2: nat, ub2: nat, comparer: spec_fn(int, int) -> bool)
    requires
        0 <= lb1 <= lb2 <= ub2 <= ub1 <= q.len(),
        range_satisfies_comparer(q, key, lb1, ub1, comparer)
    ensures
        range_satisfies_comparer(q, key, lb2, ub2, comparer)
{
    assert forall|i: int| lb2 <= i < ub2 implies comparer(q[i], key) by {
        assert(lb1 <= i < ub1);
    };
}

proof fn lemma_range_satisfies_comparer_negation_monotonic(q: Seq<int>, key: int, lb1: nat, ub1: nat, lb2: nat, ub2: nat, comparer: spec_fn(int, int) -> bool)
    requires
        0 <= lb1 <= lb2 <= ub2 <= ub1 <= q.len(),
        range_satisfies_comparer_negation(q, key, lb1, ub1, comparer)
    ensures
        range_satisfies_comparer_negation(q, key, lb2, ub2, comparer)
{
    assert forall|i: int| lb2 <= i < ub2 implies !comparer(q[i], key) by {
        assert(lb1 <= i < ub1);
    };
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
    
    proof {
        lemma_comparer_properties(comparer);
        lemma_transitivity_ge();
        lemma_transitivity_gt();
        lemma_ge_implies_gt_or_eq();
    }
    
    while low < high
        invariant
            lower_bound <= low <= high <= upper_bound,
            range_satisfies_comparer_negation(q, key, lower_bound as nat, low as nat, comparer),
            range_satisfies_comparer(q, key, high as nat, upper_bound as nat, comparer),
        decreases high - low
    {
        let mid = low + (high - low) / 2;
        let mid_int: int = mid as int;
        
        proof {
            assert(low <= mid < high) by {
                assert(mid >= low);
                assert(mid < high);
            };
        }
        
        if comparer(q[mid_int], key) {
            proof {
                if comparer_is_ge(comparer) {
                    assert forall|i: int| mid_int <= i < high as int implies comparer(q[i], key) by {
                        lemma_sorted_property(q, mid_int, i);
                        assert(q[mid_int] <= q[i]);
                        assert(comparer(q[mid_int], key));
                        assert(q[mid_int] >= key);
                        assert(q[i] >= q[mid_int]);
                        assert(q[i] >= key);
                        assert(comparer(q[i], key));
                    };
                } else {
                    assert(comparer_is_gt(comparer));
                    assert forall|i: int| mid_int <= i < high as int implies comparer(q[i], key) by {
                        lemma_sorted_property(q, mid_int, i);
                        assert(q[mid_int] <= q[i]);
                        assert(comparer(q[mid_int], key));
                        assert(q[mid_int] > key);
                        if q[i] == q[mid_int] {
                            assert(q[i] > key);
                        } else {
                            assert(q[i] > q[mid_int]);
                            assert(q[i] > key);
                        };
                        assert(comparer(q[i], key));
                    };
                };
                lemma_range_satisfies_comparer_monotonic(q, key, high as nat, upper_bound as nat, mid as nat, upper_bound as nat, comparer);
            }
            high = mid;
        } else {
            proof {
                if comparer_is_ge(comparer) {
                    assert forall|i: int| low as int <= i <= mid_int implies !comparer(q[i], key) by {
                        lemma_sorted_property(q, i, mid_int);
                        assert(q[i] <= q[mid_int]);
                        assert(!comparer(q[mid_int], key));
                        assert(!(q[mid_int] >= key));
                        assert(q[mid_int] < key);
                        assert(q[i] <= q[mid_int]);
                        assert(q[i] < key);
                        assert(!(q[i] >= key));
                        assert(!comparer(q[i], key));
                    };
                } else {
                    assert(comparer_is_gt(comparer));
                    assert forall|i: int| low as int <= i <= mid_int implies !comparer(q[i], key) by {
                        lemma_sorted_property(q, i, mid_int);
                        assert(q[i] <= q[mid_int]);
                        assert(!comparer(q[mid_int], key));
                        assert(!(q[mid_int] > key));
                        assert(q[mid_int] <= key);
                        assert(q[i] <= q[mid_int]);
                        assert(q[i] <= key);
                        assert(!(q[i] > key));
                        assert(!comparer(q[i], key));
                    };
                };
                lemma_range_satisfies_comparer_negation_monotonic(q, key, lower_bound as nat, low as nat, lower_bound as nat, (mid + 1) as nat, comparer);
            }
            low = mid + 1;
        }
    }
    
    proof {
        assert(range_satisfies_comparer_negation(q, key, lower_bound as nat, low as nat, comparer));
        assert(range_satisfies_comparer(q, key, low as nat, q.len() as nat, comparer));
    }
    
    low
}
// </vc-code>

fn main() {
}

}