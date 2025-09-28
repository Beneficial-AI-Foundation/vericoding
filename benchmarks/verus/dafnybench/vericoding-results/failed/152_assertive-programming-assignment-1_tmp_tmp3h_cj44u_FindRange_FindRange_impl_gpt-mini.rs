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
proof fn comparer_ge_suffix(q: Seq<int>, key: int, idx: usize, comparer: spec_fn(int, int) -> bool)
    requires sorted(q)
    requires forall |n1: int, n2: int| #[trigger] comparer(n1, n2) == (n1 >= n2)
    requires idx < q.len()
    requires comparer(q@[idx], key)
    ensures forall |j: int| idx as int <= j < q.len() as int ==> comparer(q@[j as usize], key)
{
    forall(|j: int| {
        if idx as int <= j && j < q.len() as int {
            // q[j] >= q[idx] by sortedness
            assert(q@[j as usize] >= q@[idx]);
            // comparer(...) == (n1 >= n2)
            assert(comparer(q@[idx], key) == (q@[idx] >= key));
            assert(q@[idx] >= key);
            assert(q@[j as usize] >= key);
            assert(comparer(q@[j as usize], key));
        }
    });
}

proof fn comparer_ge_prefix(q: Seq<int>, key: int, idx: usize, comparer: spec_fn(int, int) -> bool)
    requires sorted(q)
    requires forall |n1: int, n2: int| #[trigger] comparer(n1, n2) == (n1 >= n2)
    requires idx < q.len()
    requires !comparer(q@[idx], key)
    ensures forall |i: int| 0 <= i <= idx as int ==> !comparer(q@[i as usize], key)
{
    forall(|i: int| {
        if 0 <= i && i <= idx as int {
            // q[i] <= q[idx] by sortedness
            assert(q@[i as usize] <= q@[idx]);
            // !comparer(q[idx], key) -> !(q[idx] >= key) -> q[idx] < key
            assert(comparer(q@[idx], key) == (q@[idx] >= key));
            assert(!(q@[idx] >= key));
            assert(q@[idx] < key);
            assert(q@[i as usize] < key);
            assert(!comparer(q@[i as usize], key));
        }
    });
}

proof fn comparer_gt_suffix(q: Seq<int>, key: int, idx: usize, comparer: spec_fn(int, int) -> bool)
    requires sorted(q)
    requires forall |n1: int, n2: int| #[trigger] comparer(n1, n2) == (n1 > n2)
    requires idx < q.len()
    requires comparer(q@[idx], key)
    ensures forall |j: int| idx as int <= j < q.len() as int ==> comparer(q@[j as usize], key)
{
    forall(|j: int| {
        if idx as int <= j && j < q.len() as int {
            // q[j] >= q[idx] by sortedness
            assert(q@[j as usize] >= q@[idx]);
            // comparer(q[idx], key) == (q[idx] > key)
            assert(comparer(q@[idx], key) == (q@[idx] > key));
            assert(q@[idx] > key);
            // q[j] >= q[idx] and q[idx] > key => q[j] > key
            assert(q@[j as usize] > key);
            assert(comparer(q@[j as usize], key));
        }
    });
}

proof fn comparer_gt_prefix(q: Seq<int>, key: int, idx: usize, comparer: spec_fn(int, int) -> bool)
    requires sorted(q)
    requires forall |n1: int, n2: int| #[trigger] comparer(n1, n2) == (n1 > n2)
    requires idx < q.len()
    requires !comparer(q@[idx], key)
    ensures forall |i: int| 0 <= i <= idx as int ==> !comparer(q@[i as usize], key)
{
    forall(|i: int| {
        if 0 <= i && i <= idx as int {
            // q[i] <= q[idx]
            assert(q@[i as usize] <= q@[idx]);
            // !comparer(q[idx], key) -> !(q[idx] > key) -> q[idx] <= key
            assert(comparer(q@[idx], key) == (q@[idx] > key));
            assert(!(q@[idx] > key));
            assert(q@[idx] <= key);
            assert(q@[i as usize] <= key);
            assert(!comparer(q@[i as usize], key));
        }
    });
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
    // implement find_range by performing two concrete binary searches:
    // one for the first index with q[i] >= key (lower)
    // one for the first index with q[i] > key (upper)

    // first: find lower = first index with q[i] >= key
    let mut l: usize = 0usize;
    let mut r: usize = q.len();
    // invariants:
    // 0 <= l <= r <= q.len()
    // for all i < l: q[i] < key
    // for all i >= r: q[i] >= key
    while l < r
        invariant 0 <= l <= r <= q.len()
        invariant forall |i: int| 0 <= i && i < l as int ==> q@[i as usize] < key
        invariant forall |i: int| r as int <= i && i < q.len() as int ==> q@[i as usize] >= key
    {
        let mid: usize = l + (r - l) / 2;
        if q@[mid] >= key {
            // show suffix from mid holds: forall j >= mid => q[j] >= key
            proof {
                forall(|j: int| {
                    if mid as int <= j && j < q.len() as int {
                        // by sortedness q[j] >= q[mid]
                        assert(q@[j as usize] >= q@[mid]);
                        assert(q@[mid] >= key);
                        assert(q@[j as usize] >= key);
                    }
                });
                // prefix invariant for l is unchanged
            }
            r = mid;
        } else {
            // q[mid] < key
            // show prefix up to mid+1 holds: forall i < mid+1 => q[i] < key
            proof {
                forall(|i: int| {
                    if 0 <= i && i < (mid + 1) as int {
                        // i <= mid => q[i] <= q[mid] < key
                        assert(q@[i as usize] <= q@[mid]);
                        assert(q@[mid] < key);
                        assert(q@[i as usize] < key);
                    }
                });
                // suffix invariant for r is unchanged
            }
            l = mid + 1;
        }
    }
    let lower: usize = l;

    // second: find upper = first index with q[i] > key
    let mut l2: usize = 0usize;
    let mut r2: usize = q.len();
    // invariants:
    // 0 <= l2 <= r2 <= q.len()
    // for all i < l2: q[i] <= key
    // for all i >= r2: q[i] > key
    while l2 < r2
        invariant 0 <= l2 <= r2 <= q.len()
        invariant forall |i: int| 0 <= i && i < l2 as int ==> q@[i as usize] <= key
        invariant forall |i: int| r2 as int <= i && i < q.len() as int ==> q@[i as usize] > key
    {
        let mid: usize = l2 + (r2 - l2) / 2;
        if q@[mid] > key {
            // maintain suffix from mid: for j >= mid q[j] > key
            proof {
                forall(|j: int| {
                    if mid as int <= j && j < q.len() as int {
                        assert(q@[j as usize] >= q@[mid]);
                        assert(q@[mid] > key);
                        // q[j] >= q[mid] and q[mid] > key => q[j] > key
                        assert(q@[j as usize] > key);
                    }
                });
            }
            r2 = mid;
        } else {
            // q[mid] <= key
            // maintain prefix up to mid+1: for i < mid+1 q[i] <= key
            proof {
                forall(|i: int| {
                    if 0 <= i && i < (mid + 1) as int {
                        assert(q@[i as usize] <= q@[mid]);
                        assert(q@[mid] <= key);
                        assert(q@[i as usize] <= key);
                    }
                });
            }
            l2 = mid + 1;
        }
    }
    let upper: usize = l2;

    let res = (lower, upper);
    proof {
        // bounds: res.0 <= res.1 <= q.len()
        assert(res.1 <= q.len());

        // forall i < res.0 ==> q[i] < key
        forall(|i: int| {
            if 0 <= i && i < res.0 as int {
                assert(q@[i as usize] < key);
            }
        });

        // forall i in [res.0, res.1) ==> q[i] == key
        // From lower: for i >= lower, q[i] >= key
        // From upper: for i < upper, q[i] <= key
        forall(|i: int| {
            if res.0 as int <= i && i < res.1 as int {
                assert(q@[i as usize] >= key);
                assert(q@[i as usize] <= key);
                assert(q@[i as usize] == key);
            }
        });

        // forall i >= res.1 ==> q[i] > key
        forall(|i: int| {
            if res.1 as int <= i && i < q.len() as int {
                assert(q@[i as usize] > key);
            }
        });

        // prove lower <= upper by contradiction as described above
        if res.0 as int > res.1 as int {
            // take j = res.1
            let j: int = res.1 as int;
            // j < res.0 so by prefix before lower, q[j] < key
            assert(q@[j as usize] < key);
            // but j >= res.1, so by suffix from upper, q[j] > key
            assert(q@[j as usize] > key);
            assert(false);
        }
    }
    res
}
// </vc-code>

fn main() {
}

}