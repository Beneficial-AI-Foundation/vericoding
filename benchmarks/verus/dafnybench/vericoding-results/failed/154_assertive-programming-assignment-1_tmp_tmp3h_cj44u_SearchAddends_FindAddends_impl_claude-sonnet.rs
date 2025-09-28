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
proof fn lemma_has_addends_implies_exists_indices(q: Seq<int>, x: int)
    requires has_addends(q, x)
    ensures exists|i: nat, j: nat| are_ordered_indices(q, i, j) && are_addends_indices(q, x, i, j)
{
    assert(exists|i: int, j: int| 0 <= i < j < q.len() && q[i] + q[j] == x);
}

proof fn lemma_sorted_addends_unique(q: Seq<int>, x: int, left: nat, right: nat)
    requires 
        sorted(q),
        are_ordered_indices(q, left, right),
        are_addends_indices(q, x, left, right)
    ensures q[left as int] + q[right as int] == x
{
}

proof fn lemma_sum_too_small(q: Seq<int>, x: int, left: nat, right: nat)
    requires 
        sorted(q),
        are_ordered_indices(q, left, right),
        q[left as int] + q[right as int] < x,
        has_addends(q, x)
    ensures exists|i: nat, j: nat| are_ordered_indices(q, i, j) && i > left && are_addends_indices(q, x, i, j)
{
    assert(exists|i: int, j: int| 0 <= i < j < q.len() && q[i] + q[j] == x);
}

proof fn lemma_sum_too_large(q: Seq<int>, x: int, left: nat, right: nat)
    requires 
        sorted(q),
        are_ordered_indices(q, left, right),
        q[left as int] + q[right as int] > x,
        has_addends(q, x)
    ensures exists|i: nat, j: nat| are_ordered_indices(q, i, j) && j < right && are_addends_indices(q, x, i, j)
{
    assert(exists|i: int, j: int| 0 <= i < j < q.len() && q[i] + q[j] == x);
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
    let mut left: usize = 0;
    let mut right: usize = (q.len() - 1) as int as usize;
    
    proof {
        lemma_has_addends_implies_exists_indices(q, x);
        assert(exists|i: nat, j: nat| are_ordered_indices(q, i, j) && are_addends_indices(q, x, i, j));
    }
    
    while left < right
        invariant 
            0 <= left < q.len(),
            left <= right < q.len(),
            has_addends(q, x),
            sorted(q),
            exists|i: nat, j: nat| left <= i < j <= right && are_addends_indices(q, x, i, j)
    {
        let ghost sum = q[left as int] + q[right as int];
        
        if sum == x {
            return (left, right);
        } else if sum < x {
            proof {
                lemma_sum_too_small(q, x, left as nat, right as nat);
            }
            left = left + 1;
        } else {
            proof {
                lemma_sum_too_large(q, x, left as nat, right as nat);
            }
            right = right - 1;
        }
    }
    
    unreached()
}
// </vc-code>

fn main() {
}

}