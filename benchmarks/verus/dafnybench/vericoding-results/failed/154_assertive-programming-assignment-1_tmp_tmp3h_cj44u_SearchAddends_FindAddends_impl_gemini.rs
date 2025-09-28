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
/* helper modified by LLM (iteration 5): fixed Seq indexing syntax from q@i to q[i] */
proof fn lemma_sum_lt(q: Seq<int>, x: int, i: int, j: int)
    requires
        sorted(q),
        0 <= i < j < q.len(),
        q[i] + q[j] < x,
        exists |a: int, b: int| i <= a < b <= j && q[a] + q[b] == x,
    ensures
        exists |a: int, b: int| i + 1 <= a < b <= j && q[a] + q[b] == x,
{
    let (a, b) = choose |a: int, b: int| i <= a < b <= j && q[a] + q[b] == x;
    if a == i {
        assert(sorted(q));
        assert(q[b] <= q[j]);
        assert(q[i] + q[b] <= q[i] + q[j]);
        assert(x <= q[i] + q[j]);
        assert(false); // Contradicts `q[i] + q[j] < x`
    }
    assert(a >= i + 1);
}

/* helper modified by LLM (iteration 5): fixed Seq indexing syntax from q@i to q[i] */
proof fn lemma_sum_gt(q: Seq<int>, x: int, i: int, j: int)
    requires
        sorted(q),
        0 <= i < j < q.len(),
        q[i] + q[j] > x,
        exists |a: int, b: int| i <= a < b <= j && q[a] + q[b] == x,
    ensures
        exists |a: int, b: int| i <= a < b <= j - 1 && q[a] + q[b] == x,
{
    let (a, b) = choose |a: int, b: int| i <= a < b <= j && q[a] + q[b] == x;
    if b == j {
        assert(sorted(q));
        assert(q[a] >= q[i]);
        assert(q[a] + q[j] >= q[i] + q[j]);
        assert(x >= q[i] + q[j]);
        assert(false); // Contradicts `q[i] + q[j] > x`
    }
    assert(b <= j - 1);
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
/* code modified by LLM (iteration 5): implemented a two-pointer search algorithm */
{
    let mut i: usize = 0;
    let mut j: usize = q.len() - 1;

    while i < j
        invariant
            0 <= i < j < q.len(),
            sorted(q),
            exists |a: int, b: int| (i as int) <= a < b <= (j as int) && q[a] + q[b] == x,
        decreases (j - i) as int
    {
        let sum = q[i as int] + q[j as int];
        if sum == x {
            return (i, j);
        } else if sum < x {
            lemma_sum_lt(q, x, i as int, j as int);
            i = i + 1;
        } else { // sum > x
            lemma_sum_gt(q, x, i as int, j as int);
            j = j - 1;
        }
    }
    
    unreachable();
}
// </vc-code>

}
fn main() {}