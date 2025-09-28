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
proof fn lemma_seq_subrange_has_addends(q: Seq<int>, x: int, start: nat, end: nat)
    requires
        sorted(q) && has_addends(q, x),
        0 <= start <= end <= q.len(),
    ensures
        has_addends_in_indices_range(q, x, start, end) || (exists|k: nat| k < start && has_addends_in_indices_range(q, x, k, end))
{
}

proof fn lemma_pair_exists_in_subrange(q: Seq<int>, x: int, i: nat, j: nat)
    requires
        sorted(q) && are_ordered_indices(q, i, j),
        q[i] + q[j] > x,
    ensures
        !are_addends_indices(q, x, i, j) && has_addends_in_indices_range(q, x, i, (j - 1) as nat)
{
}

proof fn lemma_pair_exists_in_subrange2(q: Seq<int>, x: int, i: nat, j: nat)
    requires
        sorted(q) && are_ordered_indices(q, i, j),
        q[i] + q[j] < x,
    ensures
        !are_addends_indices(q, x, i, j) && has_addends_in_indices_range(q, x, (i + 1) as nat, j)
{
}

proof fn lemma_addends_preserved_when_shrinking(q: Seq<int>, x: int, i1: nat, j1: nat, i2: nat, j2: nat)
    requires
        sorted(q) && has_addends_in_indices_range(q, x, i1, j1),
        i2 <= i1 <= j1 <= j2 < q.len(),
    ensures
        has_addends_in_indices_range(q, x, i2, j2)
{
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
    let n = q.len();
    let mut i: usize = 0;
    let mut j: usize = n - 1;
    while i < j
        invariant
            0 <= i <= j < n,
            has_addends_in_indices_range(q, x, i as nat, j as nat),
        decreases j - i
    {
        let sum = q[i] + q[j];
        if sum == x {
            return (i, j);
        } else if sum > x {
            proof {
                lemma_pair_exists_in_subrange(q, x, i as nat, j as nat);
            }
            j = j - 1;
        } else {
            proof {
                lemma_pair_exists_in_subrange2(q, x, i as nat, j as nat);
            }
            i = i + 1;
        }
    }
    proof {
        assert(has_addends_in_indices_range(q, x, i as nat, j as nat));
        assert(i < j < n && q[i] + q[j] == x) by {
            assert(are_ordered_indices(q, i as nat, j as nat));
        }
    }
    (i, j)
}
// </vc-code>

fn main() {
}

}