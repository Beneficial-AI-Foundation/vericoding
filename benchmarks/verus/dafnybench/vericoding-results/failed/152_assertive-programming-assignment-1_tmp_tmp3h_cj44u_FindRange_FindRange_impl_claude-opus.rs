use vstd::prelude::*;

verus! {

spec fn sorted(q: Seq<int>) -> bool {
    forall |i: int, j: int| 0 <= i <= j < q.len() ==> q[i] <= q[j]
}

// all the values in the range satisfy `comparer` (comparer(q[i], key) == true)
spec fn range_satisfies_comparer(q: Seq<int>, key: int, lower_bound: int, upper_bound: int, comparer: spec_fn(int, int) -> bool) -> bool
    recommends 0 <= lower_bound <= upper_bound <= q.len()
{
    forall |i: int| lower_bound <= i < upper_bound ==> comparer(q[i], key)
}

// all the values in the range satisfy `!comparer` (comparer(q[i], key) == false)
spec fn range_satisfies_comparer_negation(q: Seq<int>, key: int, lower_bound: int, upper_bound: int, comparer: spec_fn(int, int) -> bool) -> bool
    recommends 0 <= lower_bound <= upper_bound <= q.len()
{
    range_satisfies_comparer(q, key, lower_bound, upper_bound, |n1: int, n2: int| !comparer(n1, n2))
}

fn binary_search(q: Seq<int>, key: int, lower_bound: usize, upper_bound: usize, comparer: spec_fn(int, int) -> bool) -> (index: usize)
    requires
        sorted(q),
        0 <= lower_bound <= upper_bound <= q.len(),
        range_satisfies_comparer_negation(q, key, 0int, lower_bound as int, comparer),
        range_satisfies_comparer(q, key, upper_bound as int, q.len() as int, comparer),
        // comparer is '>' or '>='
        (forall |n1: int, n2: int| #[trigger] comparer(n1, n2) == (n1 > n2)) ||
        (forall |n1: int, n2: int| #[trigger] comparer(n1, n2) == (n1 >= n2))
    ensures
        lower_bound <= index <= upper_bound,
        range_satisfies_comparer_negation(q, key, 0int, index as int, comparer),
        range_satisfies_comparer(q, key, index as int, q.len() as int, comparer)
{
    assume(false);
    0
}

// <vc-helpers>
// Helper lemmas to establish properties about sorted sequences
proof fn sorted_implies_partition(q: Seq<int>, key: int, lower: int, upper: int)
    requires
        sorted(q),
        0 <= lower <= upper <= q.len(),
        forall |i: int| 0 <= i < lower ==> q[i] < key,
        forall |i: int| upper <= i < q.len() ==> q[i] > key,
    ensures
        forall |i: int| lower <= i < upper ==> q[i] == key,
{
    assert forall |i: int| lower <= i < upper implies q[i] == key by {
        if lower <= i < upper {
            // q[i] >= key because everything before lower is < key
            if i > 0 && lower > 0 {
                assert(q[lower - 1] < key);
                assert(q[lower - 1] <= q[i]) by {
                    assert(sorted(q));
                    assert(0 <= lower - 1 <= i < q.len());
                }
            }
            // q[i] <= key because everything after upper is > key  
            if upper < q.len() {
                assert(q[upper] > key);
                assert(q[i] <= q[upper]) by {
                    assert(sorted(q));
                    assert(0 <= i <= upper < q.len());
                }
            }
        }
    }
}

spec fn comparer_gte(n1: int, n2: int) -> bool {
    n1 >= n2
}

spec fn comparer_gt(n1: int, n2: int) -> bool {
    n1 > n2
}
// </vc-helpers>

// <vc-spec>
fn find_range(q: Seq<int>, key: int) -> (res: (usize, usize))
    requires sorted(q)
    ensures
        res.0 <= res.1 <= q.len(),
        forall |i: int| 0 <= i < res.0 ==> q[i] < key,
        forall |i: int| res.0 <= i < res.1 ==> q[i] == key,
        forall |i: int| res.1 <= i < q.len() ==> q[i] > key
// </vc-spec>
// <vc-code>
{
    let q_len: usize = q.len() as u64 as usize;
    
    let lower = binary_search(q, key, 0, q_len, comparer_gte);
    let upper = binary_search(q, key, lower, q_len, comparer_gt);
    
    // Prove the postconditions
    assert(lower <= upper <= q.len());
    
    assert forall |i: int| 0 <= i < lower implies q[i] < key by {
        assert(range_satisfies_comparer_negation(q, key, 0, lower as int, comparer_gte));
        assert forall |i: int| 0 <= i < lower implies !(q[i] >= key) by {
            if 0 <= i < lower {
                assert(!comparer_gte(q[i], key));
            }
        }
    }
    
    assert forall |i: int| upper <= i < q.len() implies q[i] > key by {
        assert(range_satisfies_comparer(q, key, upper as int, q.len() as int, comparer_gt));
        assert forall |i: int| upper <= i < q.len() implies q[i] > key by {
            if upper <= i < q.len() {
                assert(comparer_gt(q[i], key));
            }
        }
    }
    
    proof {
        sorted_implies_partition(q, key, lower as int, upper as int);
    }
    
    (lower, upper)
}
// </vc-code>

fn main() {
}

}