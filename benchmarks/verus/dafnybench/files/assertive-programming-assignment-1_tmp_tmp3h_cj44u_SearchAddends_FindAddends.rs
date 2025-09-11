// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn sorted(q: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i <= j < q.len() ==> q[i] <= q[j]
}

spec fn has_addends(q: Seq<int>, x: int) -> bool {
    exists|i: int, j: int| 0 <= i < j < q.len() && q[i] + q[j] == x
}

spec fn is_valid_index<T>(q: Seq<T>, i: nat) -> bool {
    0 <= i < q.len()
}

spec fn are_ordered_indices<T>(q: Seq<T>, i: nat, j: nat) -> bool {
    0 <= i < j < q.len()
}

spec fn are_addends_indices(q: Seq<int>, x: int, i: nat, j: nat) -> bool
    recommends is_valid_index(q, i) && is_valid_index(q, j)
{
    q[i as int] + q[j as int] == x
}

spec fn has_addends_in_indices_range(q: Seq<int>, x: int, i: nat, j: nat) -> bool
    recommends are_ordered_indices(q, i, j)
{
    has_addends(q.subrange(i as int, (j + 1) as int), x)
}

spec fn loop_inv(q: Seq<int>, x: int, i: nat, j: nat, sum: int) -> bool {
    are_ordered_indices(q, i, j) &&
    has_addends_in_indices_range(q, x, i, j) &&
    are_addends_indices(q, sum, i, j)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn find_addends(q: Seq<int>, x: int) -> (result: (usize, usize))
    requires sorted(q) && has_addends(q, x)
    ensures ({
        let (i, j) = result;
        i < j < q.len() && q[i as int] + q[j as int] == x
    })
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}