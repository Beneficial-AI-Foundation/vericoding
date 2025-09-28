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

// <vc-helpers>
proof fn has_addends_nat_exists(q: Seq<int>, x: int)
    requires has_addends(q, x)
    ensures exists|i: nat, j: nat| 0 <= i < j < q.len() && q[i as int] + q[j as int] == x
{
    let (ii, jj) = choose|i: int, j: int| 0 <= i < j < q.len() && q[i] + q[j] == x;

    assert(0 <= ii && 0 <= jj);
    assert(ii < jj);
    assert(jj < q.len());

    let i_n: nat = ii as nat;
    let j_n: nat = jj as nat;

    assert((i_n as int) == ii);
    assert((j_n as int) == jj);

    assert(i_n < j_n);
    assert(j_n < q.len());
    assert(q[i_n as int] + q[j_n as int] == x);

    assert(exists|i: nat, j: nat| 0 <= i < j < q.len() && q[i as int] + q[j as int] == x);
}
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
    let (ii, jj) = choose|i: int, j: int| 0 <= i < j < q.len() && #[trigger] (q[i] + q[j]) == x;
    let result = (ii as usize, jj as usize);
    assert(result.0 < result.1);
    assert(result.1 < q.len());
    assert(q[result.0 as int] + q[result.1 as int] == x);
    result
}
// </vc-code>

fn main() {
}

}