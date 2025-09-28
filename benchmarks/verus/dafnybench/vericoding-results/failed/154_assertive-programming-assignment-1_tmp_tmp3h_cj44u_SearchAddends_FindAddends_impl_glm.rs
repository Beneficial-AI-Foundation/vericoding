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
proof fn lemma_sorted_subrange_is_sorted(q: Seq<int>, i: int, j: int)
    requires
        0 <= i <= j <= q.len(),
        sorted(q),
    ensures
        sorted(q.subrange(i, j))
{
    forall |k: int, l: int|
        0 <= k <= l < (j - i) ==> q.subrange(i, j)[k] <= q.subrange(i, j)[l]
    by {
        assert(q.subrange(i, j)[k] == q[k + i]);
        assert(q.subrange(i, j)[l] == q[l + i]);
        assert(i + k <= i + l);
        assert(k + i < j);
        assert(l + i < j);
        assert(q[k + i] <= q[l + i]);
    }
}

proof fn lemma_has_addends_in_implies_has_addends(q: Seq<int>, x: int, i: nat, j: nat, k: nat, l: nat)
    requires
        has_addends_in_indices_range(q, x, i, j),
        has_addends(q.subrange(i as int, (j + 1) as int), x),
        exists|i_: int, j_: int| 0 <= i_ < j_ < (j - i + 1) && q.subrange(i as int, (j + 1) as int)[i_] + q.subrange(i as int, (j + 1) as int)[j_] == x,
    ensures
        has_addends(q, x),
        0 <= (i + k) as int < (i + l) as int < q.len(),
        q[(i + k) as int] + q[(i + l) as int] == x
{
    let (k_, l_) = choose|i_: int, j_: int| 0 <= i_ < j_ < (j - i + 1) && q.subrange(i as int, (j + 1) as int)[i_] + q.subrange(i as int, (j + 1) as int)[j_] == x;
    assert(q.subrange(i as int, (j + 1) as int)[k_] == q[k_ + i as int]);
    assert(q.subrange(i as int, (j + 1) as int)[l_] == q[l_ + i as int]);
    assert(k_ + i as int >= i as int);
    assert(l_ + i as int < (j + 1) as int);
    assert(i as int <= k_ + i as int < l_ + i as int < q.len());
    assert(q[k_ + i as int] + q[l_ + i as int] == x);
}

proof fn lemma_sorted_has_addends_two_pointer(q: Seq<int>, x: int, i: nat, j: nat, sum: int)
    requires
        sorted(q),
        are_ordered_indices(q, i, j),
        has_addends_in_indices_range(q, x, i, j),
        i <= i < q.len(),
        j <= j < q.len(),
        i < j,
        q[i as int] + q[j as int] == sum,
        sum < x,
    ensures
        has_addends_in_indices_range(q, x, i + 1, j),
        forall|a: nat, b: nat| (a == i || b == j) && (a < b) && a >= i && b <= j ==> q[a as int] + q[b as int] < x
{
    assert(sorted(q.subrange(i as int, (j + 1) as int)));
    forall|k_: int, l_: int| 0 <= k_ <= l_ < (j - i + 1) ==> q.subrange(i as int, (j + 1) as int)[k_] <= q.subrange(i as int, (j + 1) as int)[l_];
    
    assert(q[i as int] + q[j as int] < x);
    forall|a: nat, b: nat|
        (a == i || b == j) && (a < b) && a >= i && b <= j ==> q[a as int] + q[b as int] < x
    {
        if a == i {
            assert(q[a as int] + q[b as int] <= q[a as int] + q[j as int]);
            assert(q[a as int] + q[b as int] < x);
        } else {
            assert(b == j);
            assert(q[a as int] + q[b as int] <= q[j as int] + q[b as int]);
            assert(q[a as int] + q[b as int] < x);
        }
    }
    
    exists|i_: int, j_: int| 0 <= i_ < j_ < (j - (i + 1) + 1) && q.subrange((i + 1) as int, (j + 1) as int)[i_] + q.subrange((i + 1) as int, (j + 1) as int)[j_] == x
    {
        let (i__, j__) = choose|i_: int, j_: int| 0 <= i_ < j_ < (j - i + 1) && q.subrange(i as int, (j + 1) as int)[i_] + q.subrange(i as int, (j + 1) as int)[j_] == x;
        assert(i__ > 0);
        let new_i_ = i__ - 1;
        let new_j_ = j__ - 1;
        
        assert(0 <= new_i_ < new_j_ < (j - i));
        assert(q.subrange((i + 1) as int, (j + 1) as int)[new_i_] == q[new_i_ + (i + 1) as int]);
        assert(q.subrange((i + 1) as int, (j + 1) as int)[new_j_] == q[new_j_ + (i + 1) as int]);
        
        assert(q.subrange(i as int, (j + 1) as int)[i__] == q[new_i_ + (i + 1) as int]);
        assert(q.subrange(i as int, (j + 1) as int)[j__] == q[new_j_ + (i + 1) as int]);
        
        assert(q[new_i_ + (i + 1) as int] + q[new_j_ + (i + 1) as int] == x);
        assert(q.subrange((i + 1) as int, (j + 1) as int)[new_i_] + q.subrange((i + 1) as int, (j + 1) as int)[new_j_] == x);
    }
}

proof fn lemma_sorted_has_addends_two_pointer_decrease_j(q: Seq<int>, x: int, i: nat, j: nat, sum: int)
    requires
        sorted(q),
        are_ordered_indices(q, i, j),
        has_addends_in_indices_range(q, x, i, j),
        i <= i < q.len(),
        j <= j < q.len(),
        i < j,
        q[i as int] + q[j as int] == sum,
        sum > x,
    ensures
        has_addends_in_indices_range(q, x, i, j - 1),
        forall|a: nat, b: nat| (a == i || b == j) && (a < b) && a >= i && b <= j ==> q[a as int] + q[b as int] > x
{
    assert(sorted(q.subrange(i as int, (j + 1) as int)));
    forall|k_: int, l_: int| 0 <= k_ <= l_ < (j - i + 1) ==> q.subrange(i as int, (j + 1) as int)[k_] <= q.subrange(i as int, (j + 1) as int)[l_];
    
    assert(q[i as int] + q[j as int] > x);
    forall|a: nat, b: nat|
        (a == i || b == j) && (a < b) && a >= i && b <= j ==> q[a as int] + q[b as int] > x
    {
        if a == i {
            assert(q[a as int] + q[b as int] >= q[a as int] + q[i as int]);
            assert(q[a as int] + q[b as int] > x);
        } else {
            assert(b == j);
            assert(q[a as int] + q[b as int] >= q[i as int] + q[b as int]);
            assert(q[a as int] + q[b as int] > x);
        }
    }
    
    exists|i_: int, j_: int| 0 <= i_ < j_ < ((j - 1) - i + 1) && q.subrange(i as int, (j - 1 + 1) as int)[i_] + q.subrange(i as int, (j - 1 + 1) as int)[j_] == x
    {
        let (i__, j__) = choose|i_: int, j_: int| 0 <= i_ < j_ < (j - i + 1) && q.subrange(i as int, (j + 1) as int)[i_] + q.subrange(i as int, (j + 1) as int)[j_] == x;
        assert(j__ < j - i);
        
        assert(0 <= i__ < j__ < (j - i));
        assert(q.subrange(i as int, (j - 1 + 1) as int)[i__] == q[i__ + i as int]);
        assert(q.subrange(i as int, (j - 1 + 1) as int)[j__] == q[j__ + i as int]);
        
        assert(q.subrange(i as int, (j + 1) as int)[i__] == q[i__ + i as int]);
        assert(q.subrange(i as int, (j + 1) as int)[j__] == q[j__ + i as int]);
        
        assert(q[i__ + i as int] + q[j__ + i as int] == x);
        assert(q.subrange(i as int, (j - 1 + 1) as int)[i__] + q.subrange(i as int, (j - 1 + 1) as int)[j__] == x);
    }
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
    let mut i: usize = 0;
    let mut j: usize = q.len() - 1;
    
    proof {
        assert(q.len() >= 2);
        lemma_sorted_subrange_is_sorted(q, 0, q.len() as int);
        lemma_has_addends_in_implies_has_addends(q, x, 0, (q.len() - 1) as nat, 0, (q.len() - 1) as nat);
    }
    
    while i < j
        invariant
            0 <= i < q.len(),
            0 <= j < q.len(),
            i <= j,
            has_addends_in_indices_range(q, x, i as nat, j as nat),
    {
        let sum = q[i as int] + q[j as int];
        
        if sum == x {
            proof {
                assert(has_addends(q, x));
                assert(q[i as int] + q[j as int] == x);
            }
            return (i, j);
        } else if sum < x {
            proof {
                lemma_sorted_has_addends_two_pointer(q, x, i as nat, j as nat, sum);
            }
            i += 1;
        } else {
            proof {
                lemma_sorted_has_addends_two_pointer_decrease_j(q, x, i as nat, j as nat, sum);
            }
            j -= 1;
        }
    }
    
    proof {
        assert(false);
    }
    
    unreachable!()
}
// </vc-code>

fn main() {
}

}