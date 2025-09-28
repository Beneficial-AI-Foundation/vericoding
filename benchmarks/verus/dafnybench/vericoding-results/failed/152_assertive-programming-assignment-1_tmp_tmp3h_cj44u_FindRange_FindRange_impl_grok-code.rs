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
fn binary_search(q: Seq<int>, key: int, lower: usize, upper: usize, comparer: Fn(int, int) -> bool) -> (index: usize)
    requires
        sorted(q),
        0 <= lower <= upper <= q.len(),
        range_satisfies_comparer_negation(q, key, 0, lower as int, |n1, n2| !comparer(n1, n2)),
        range_satisfies_comparer(q, key, upper as int, q.len() as int, comparer),
        // comparer is '>' or '>='
        (forall |n1: int, n2: int| #[trigger] comparer(n1, n2) == (n1 > n2)) ||
        (forall |n1: int, n2: int| #[trigger] comparer(n1, n2) == (n1 >= n2))
    ensures
        lower <= index <= upper,
        range_satisfies_comparer_negation(q, key, 0, index as int, |n1, n2| !comparer(n1, n2)),
        range_satisfies_comparer(q, key, index as int, q.len() as int, comparer)
{
    let mut i = lower;
    let mut j = upper;
    while i < j
        invariant
            lower <= i <= j <= upper,
            range_satisfies_comparer_negation(q, key, 0, i as int, |n1, n2| !comparer(n1, n2)),
            range_satisfies_comparer(q, key, j as int, q.len() as int, comparer)
    {
        let mid = (i + j) / 2;
        proof {
            let ghost mid_int = mid as int;
            assert(0 <= mid_int < q.len());
        }
        if comparer(q@[mid as int], key) {
            j = mid;
        } else {
            i = mid + 1;
        }
    }
    proof {
        assert(range_satisfies_comparer_negation(q, key, 0, i as int, |n1, n2| !comparer(n1, n2)));
        assert(range_satisfies_comparer(q, key, i as int, q.len() as int, comparer));
    }
    i
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
    assert(sorted(q));
    let l = binary_search(q, key, 0, q.len() as usize, |x: int, y: int| x >= y);
    proof {
        let ghost l_int = l as int;
    }
    let res = if l < q.len() as usize && q@[l as int] == key {
        let u = binary_search(q, key, l, q.len() as usize, |x: int, y: int| x > y);
        (l, u)
    } else {
        (l, l)
    };
    res
}
// </vc-code>

fn main() {
}

}