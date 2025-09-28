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
proof fn lemma_sorted_subrange(q: Seq<int>, i: nat, j: nat)
    requires 
        sorted(q),
        are_ordered_indices(q, i, j),
    ensures 
        sorted(q.subrange(i as int, (j + 1) as int))
{
    assert forall|a: int, b: int| 0 <= a <= b < q.subrange(i as int, (j + 1) as int).len() implies
        #[trigger] q.subrange(i as int, (j + 1) as int)[a] <= q.subrange(i as int, (j + 1) as int)[b]
    by {
        assert(q.subrange(i as int, (j + 1) as int)[a] == q[i + a]);
        assert(q.subrange(i as int, (j + 1) as int)[b] == q[i + b]);
        assert(q[i + a] <= q[i + b]);
    }
}

proof fn lemma_has_addends_shrink_left(q: Seq<int>, x: int, i: nat, j: nat, sum: int)
    requires
        sorted(q),
        are_ordered_indices(q, i, j),
        has_addends_in_indices_range(q, x, i, j),
        are_addends_indices(q, sum, i, j),
        sum < x,
        i + 1 < j,
    ensures
        has_addends_in_indices_range(q, x, (i + 1) as nat, j),
{
    let sub = q.subrange(i as int, (j + 1) as int);
    let (a, b) = choose|a: int, b: int| 0 <= a < b < sub.len() && sub[a] + sub[b] == x;
    
    assert(sub[a] == q[i + a]);
    assert(sub[b] == q[i + b]);
    
    if a == 0 {
        assert(sub[0] == q[i as int]);
        assert(q[i as int] + q[(i + b) as int] == x);
        assert(q[i as int] + q[j as int] == sum);
        assert(sum < x);
        
        lemma_sorted_subrange(q, i, j);
        assert(sorted(sub));
        assert(b <= sub.len() - 1);
        assert(sub[b] <= sub[sub.len() - 1]);
        assert(q[(i + b) as int] <= q[j as int]);
        assert(q[i as int] + q[(i + b) as int] <= q[i as int] + q[j as int]);
        assert(x <= sum);
        assert(false);
    }
    
    assert(a > 0);
    let sub_next = q.subrange((i + 1) as int, (j + 1) as int);
    assert(sub_next[a - 1] == q[i + a]);
    assert(sub_next[b - 1] == q[i + b]);
    assert(sub_next[a - 1] + sub_next[b - 1] == x);
    assert(has_addends(sub_next, x));
}

proof fn lemma_has_addends_shrink_right(q: Seq<int>, x: int, i: nat, j: nat, sum: int)
    requires
        sorted(q),
        are_ordered_indices(q, i, j),
        has_addends_in_indices_range(q, x, i, j),
        are_addends_indices(q, sum, i, j),
        sum > x,
        i + 1 < j,
    ensures
        has_addends_in_indices_range(q, x, i, (j - 1) as nat),
{
    let sub = q.subrange(i as int, (j + 1) as int);
    let (a, b) = choose|a: int, b: int| 0 <= a < b < sub.len() && sub[a] + sub[b] == x;
    
    assert(sub[a] == q[i + a]);
    assert(sub[b] == q[i + b]);
    
    if b == sub.len() - 1 {
        assert(sub[sub.len() - 1] == q[j as int]);
        assert(q[(i + a) as int] + q[j as
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
proof fn lemma_sorted_subrange(q: Seq<int>, i: nat, j: nat)
    requires 
        sorted(q),
        are_ordered_indices(q, i, j),
    ensures 
        sorted(q.subrange(i as int, (j + 1) as int))
{
    assert forall|a: int, b: int| 0 <= a <= b < q.subrange(i as int, (j + 1) as int).len() implies
        #[trigger] q.subrange(i as int, (j + 1) as int)[a] <= q.subrange(i as int, (j + 1) as int)[b]
    by {
        assert(q.subrange(i as int, (j + 1) as int)[a] == q[i + a]);
        assert(q.subrange(i as int, (j + 1) as int)[b] == q[i + b]);
        assert(q[i + a] <= q[i + b]);
    }
}

proof fn lemma_has_addends_shrink_left(q: Seq<int>, x: int, i: nat, j: nat, sum: int)
    requires
        sorted(q),
        are_ordered_indices(q, i, j),
        has_addends_in_indices_range(q, x, i, j),
        are_addends_indices(q, sum, i, j),
        sum < x,
        i + 1 < j,
    ensures
        has_addends_in_indices_range(q, x, (i + 1) as nat, j),
{
    let sub = q.subrange(i as int, (j + 1) as int);
    let (a, b) = choose|a: int, b: int| 0 <= a < b < sub.len() && sub[a] + sub[b] == x;
    
    assert(sub[a] == q[i + a]);
    assert(sub[b] == q[i + b]);
    
    if a == 0 {
        assert(sub[0] == q[i as int]);
        assert(q[i as int] + q[(i + b) as int] == x);
        assert(q[i as int] + q[j as int] == sum);
        assert(sum < x);
        
        lemma_sorted_subrange(q, i, j);
        assert(sorted(sub));
        assert(b <= sub.len() - 1);
        assert(sub[b] <= sub[sub.len() - 1]);
        assert(q[(i + b) as int] <= q[j as int]);
        assert(q[i as int] + q[(i + b) as int] <= q[i as int] + q[j as int]);
        assert(x <= sum);
        assert(false);
    }
    
    assert(a > 0);
    let sub_next = q.subrange((i + 1) as int, (j + 1) as int);
    assert(sub_next[a - 1] == q[i + a]);
    assert(sub_next[b - 1] == q[i + b]);
    assert(sub_next[a - 1] + sub_next[b - 1] == x);
    assert(has_addends(sub_next, x));
}

proof fn lemma_has_addends_shrink_right(q: Seq<int>, x: int, i: nat, j: nat, sum: int)
    requires
        sorted(q),
        are_ordered_indices(q, i, j),
        has_addends_in_indices_range(q, x, i, j),
        are_addends_indices(q, sum, i, j),
        sum > x,
        i + 1 < j,
    ensures
        has_addends_in_indices_range(q, x, i, (j - 1) as nat),
{
    let sub = q.subrange(i as int, (j + 1) as int);
    let (a, b) = choose|a: int, b: int| 0 <= a < b < sub.len() && sub[a] + sub[b] == x;
    
    assert(sub[a] == q[i + a]);
    assert(sub[b] == q[i + b]);
    
    if b == sub.len() - 1 {
        assert(sub[sub.len() - 1] == q[j as int]);
        assert(q[(i + a) as int] + q[j as
// </vc-code>

fn main() {
}

}