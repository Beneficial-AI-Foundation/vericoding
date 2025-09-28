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
// Helper lemma to prove that if comparer is > or >=, and the sequence is sorted,
// then the comparer property is monotonic
proof fn sorted_comparer_monotone(q: Seq<int>, key: int, comparer: spec_fn(int, int) -> bool, i: int, j: int)
    requires
        sorted(q),
        0 <= i < j < q.len(),
        (forall|n1: int, n2: int| #[trigger] comparer(n1, n2) ==> comparer(n1, n2) == (n1 > n2)) ||
        (forall|n1: int, n2: int| #[trigger] comparer(n1, n2) ==> comparer(n1, n2) == (n1 >= n2)),
    ensures
        comparer(q[j], key) ==> comparer(q[i], key) || q[i] <= q[j],
        !comparer(q[i], key) ==> !comparer(q[j], key) || q[i] <= q[j],
{
    // The sorted property ensures q[i] <= q[j]
    assert(q[i] <= q[j]);
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
    let mut lo: usize = lower_bound;
    let mut hi: usize = upper_bound;
    
    while lo < hi
        invariant
            lower_bound <= lo <= hi <= upper_bound,
            range_satisfies_comparer_negation(q, key, lower_bound as nat, lo as nat, comparer),
            range_satisfies_comparer(q, key, hi as nat, upper_bound as nat, comparer),
    {
        let mid: usize = lo + (hi - lo) / 2;
        
        assert(lo <= mid < hi);
        
        // Evaluate comparer at runtime using a conditional expression
        let mid_val = q[mid as int];
        let cmp_result: bool = if (forall|n1: int, n2: int| #[trigger] comparer(n1, n2) ==> comparer(n1, n2) == (n1 > n2)) {
            mid_val > key
        } else {
            mid_val >= key
        };
        
        // Assert that our runtime computation matches the spec function
        proof {
            if forall|n1: int, n2: int| #[trigger] comparer(n1, n2) ==> comparer(n1, n2) == (n1 > n2) {
                assert(comparer(mid_val, key) == (mid_val > key));
            } else {
                assert(comparer(mid_val, key) == (mid_val >= key));
            }
            assert(cmp_result == comparer(mid_val, key));
        }
        
        if cmp_result {
            // q[mid] satisfies comparer, so everything from mid onwards satisfies it
            proof {
                assert(comparer(q[mid as int], key));
                
                // Prove that all elements from mid to hi satisfy comparer
                assert forall|i: int| mid <= i < hi implies comparer(q[i], key) by {
                    if mid <= i && i < hi {
                        assert(sorted(q));
                        assert(q[mid as int] <= q[i]);
                        // Since comparer is > or >=, and q[mid] satisfies it, q[i] >= q[mid] also satisfies it
                        if forall|n1: int, n2: int| #[trigger] comparer(n1, n2) ==> comparer(n1, n2) == (n1 > n2) {
                            // comparer is >
                            assert(q[mid as int] > key);
                            assert(q[i] >= q[mid as int]);
                            assert(q[i] >= q[mid as int] > key);
                            assert(q[i] > key);
                            assert(comparer(q[i], key));
                        } else {
                            // comparer is >=
                            assert(q[mid as int] >= key);
                            assert(q[i] >= q[mid as int]);
                            assert(q[i] >= q[mid as int] >= key);
                            assert(q[i] >= key);
                            assert(comparer(q[i], key));
                        }
                    }
                }
            }
            
            hi = mid;
        } else {
            // q[mid] does not satisfy comparer, so everything up to mid doesn't satisfy it
            proof {
                assert(!comparer(q[mid as int], key));
                
                // Prove that all elements from lo to mid don't satisfy comparer
                assert forall|i: int| lo <= i <= mid implies !comparer(q[i], key) by {
                    if lo <= i && i <= mid {
                        assert(sorted(q));
                        assert(q[i] <= q[mid as int]);
                        // Since comparer is > or >=, and q[mid] doesn't satisfy it, q[i] <= q[mid] also doesn't satisfy it
                        if forall|n1: int, n2: int| #[trigger] comparer(n1, n2) ==> comparer(n1, n2) == (n1 > n2) {
                            // comparer is >
                            assert(!(q[mid as int] > key));
                            assert(q[mid as int] <= key);
                            assert(q[i] <= q[mid as int]);
                            assert(q[i] <= q[mid as int] <= key);
                            assert(!(q[i] > key));
                            assert(!comparer(q[i], key));
                        } else {
                            // comparer is >=
                            assert(!(q[mid as int] >= key));
                            assert(q[mid as int] < key);
                            assert(q[i] <= q[mid as int]);
                            assert(q[i] <= q[mid as int] < key);
                            assert(q[i] < key);
                            assert(!(q[i] >= key));
                            assert(!comparer(q[i], key));
                        }
                    }
                }
            }
            
            lo = mid + 1;
        }
    }
    
    assert(lo == hi);
    
    // Prove the postcondition for the entire range [0, lo)
    proof {
        assert(range_satisfies_comparer_negation(q, key, 0nat, lo as nat, comparer)) by {
            assert forall|i: int| 0 <= i < lo as int implies !comparer(q[i], key) by {
                if 0 <= i && i < lo as int {
                    if i < lower_bound {
                        // From precondition
                        assert(range_satisfies_comparer_negation(q, key, 0nat, lower_bound as nat, comparer));
                        assert(!comparer(q[i], key));
                    } else {
                        // From loop invariant
                        assert(lower_bound <= i && i < lo);
                        assert(range_satisfies_comparer_negation(q, key, lower_bound as nat, lo as nat, comparer));
                        assert(!comparer(q[i], key));
                    }
                }
            }
        }
        
        // Prove the postcondition for the entire range [lo, q.len())
        assert(range_satisfies_comparer(q, key, lo as nat, q.len() as nat, comparer)) by {
            assert forall|i: int| lo as int <= i < q.len() implies comparer(q[i], key) by {
                if lo as int <= i && i < q.len() {
                    if i < upper_bound {
                        // From loop invariant (since lo == hi)
                        assert(hi <= i && i < upper_bound);
                        assert(range_satisfies_comparer(q, key, hi as nat, upper_bound as nat, comparer));
                        assert(comparer(q[i], key));
                    } else {
                        // From precondition
                        assert(upper_bound <= i && i < q.len());
                        assert(range_satisfies_comparer(q, key, upper_bound as nat, q.len() as nat, comparer));
                        assert(comparer(q[i], key));
                    }
                }
            }
        }
    }
    
    lo
}
// </vc-code>

fn main() {
}

}