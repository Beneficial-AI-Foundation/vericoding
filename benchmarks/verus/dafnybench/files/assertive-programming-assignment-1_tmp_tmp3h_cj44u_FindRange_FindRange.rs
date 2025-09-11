// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn sorted(q: Seq<int>) -> bool {
    forall |i: int, j: int| 0 <= i <= j < q.len() ==> q[i] <= q[j]
}

spec fn range_satisfies_comparer(q: Seq<int>, key: int, lower_bound: int, upper_bound: int, comparer: spec_fn(int, int) -> bool) -> bool
    recommends 0 <= lower_bound <= upper_bound <= q.len()
{
    forall |i: int| lower_bound <= i < upper_bound ==> comparer(q[i], key)
}

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
// </vc-preamble>

// <vc-helpers>
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
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}