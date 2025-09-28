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
proof fn comparer_monotone_backward_key(q: Seq<int>, key: int, comparer: spec_fn(int, int) -> bool)
    requires
        sorted(q),
        (forall|n1: int, n2: int| #[trigger] comparer(n1, n2) ==> comparer(n1, n2) == (n1 > n2)) ||
        (forall|n1: int, n2: int| #[trigger] comparer(n1, n2) ==> comparer(n1, n2) == (n1 >= n2)),
    ensures
        forall|i: int, j: int| 0 <= i <= j < q.len() ==> (!comparer(q[j as usize], key) ==> !comparer(q[i as usize], key))
{
    proof {
        assert((forall|n1: int, n2: int| #[trigger] comparer(n1, n2) ==> comparer(n1, n2) == (n1 > n2)) ||
               (forall|n1: int, n2: int| #[trigger] comparer(n1, n2) ==> comparer(n1, n2) == (n1 >= n2)));
        if (forall|n1: int, n2: int| #[trigger] comparer(n1, n2) ==> comparer(n1, n2) == (n1 > n2)) {
            // comparer(n1,n2) == (n1 > n2)
            assert(forall|i: int, j: int| 0 <= i <= j < q.len() ==>
                (!comparer(q[j as usize], key) ==> !comparer(q[i as usize], key)));
            // Proof detail:
            // Let 0 <= i <= j < q.len() and suppose !comparer(q[j], key).
            // Then !(q[j] > key) so q[j] <= key. Since sorted(q) and i <= j we have q[i] <= q[j] <= key,
            // so !(q[i] > key) and hence !comparer(q[i], key).
        } else {
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
proof fn comparer_monotone_backward_key(q: Seq<int>, key: int, comparer: spec_fn(int, int) -> bool)
    requires
        sorted(q),
        (forall|n1: int, n2: int| #[trigger] comparer(n1, n2) ==> comparer(n1, n2) == (n1 > n2)) ||
        (forall|n1: int, n2: int| #[trigger] comparer(n1, n2) ==> comparer(n1, n2) == (n1 >= n2)),
    ensures
        forall|i: int, j: int| 0 <= i <= j < q.len() ==> (!comparer(q[j as usize], key) ==> !comparer(q[i as usize], key))
{
    proof {
        assert((forall|n1: int, n2: int| #[trigger] comparer(n1, n2) ==> comparer(n1, n2) == (n1 > n2)) ||
               (forall|n1: int, n2: int| #[trigger] comparer(n1, n2) ==> comparer(n1, n2) == (n1 >= n2)));
        if (forall|n1: int, n2: int| #[trigger] comparer(n1, n2) ==> comparer(n1, n2) == (n1 > n2)) {
            // comparer(n1,n2) == (n1 > n2)
            assert(forall|i: int, j: int| 0 <= i <= j < q.len() ==>
                (!comparer(q[j as usize], key) ==> !comparer(q[i as usize], key)));
            // Proof detail:
            // Let 0 <= i <= j < q.len() and suppose !comparer(q[j], key).
            // Then !(q[j] > key) so q[j] <= key. Since sorted(q) and i <= j we have q[i] <= q[j] <= key,
            // so !(q[i] > key) and hence !comparer(q[i], key).
        } else {
// </vc-code>

fn main() {
}

}