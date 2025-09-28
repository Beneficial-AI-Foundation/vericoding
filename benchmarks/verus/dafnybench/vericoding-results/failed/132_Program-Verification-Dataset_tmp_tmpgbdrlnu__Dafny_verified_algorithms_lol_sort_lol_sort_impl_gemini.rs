// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_permut(a: Seq<int>, b: Seq<int>) -> bool
    recommends a.len() == b.len()
{
    a.to_multiset() == b.to_multiset()
}

fn swap(a: &mut Vec<int>, i: usize, j: usize)
    requires 
        i < old(a).len(),
        j < old(a).len(),
    ensures
        a.len() == old(a).len(),
        a@ == old(a)@.update(i as int, old(a)[j as int]).update(j as int, old(a)[i as int]),
        valid_permut(a@, old(a)@),
{
    assume(false);
}

spec fn sorted(a: Seq<int>) -> bool
{
    forall|i: int, j: int| 0 <= i <= j < a.len() ==> a[i] <= a[j]
}
// </vc-preamble>

// <vc-helpers>
fn find_min_index(a: &Vec<int>, start: usize) -> (min_idx: usize)
    requires
        start < a.len(),
    ensures
        start <= min_idx < a.len(),
        forall|k: int| start <= k < a.len() ==> a@[min_idx as int] <= a@[k as int],
        exists|k: int| start <= k < a.len() && a@[min_idx as int] == a@[k as int],
{
    let mut min_idx = start;
    let mut j = start + 1;
    while j < a.len()
        invariant
            start < a.len(),
            start < j <= a.len(),
            start <= min_idx < j,
            forall|k: int| start <= k < j ==> a@[min_idx as int] <= a@[k as int],
            exists|k: int| start <= k < j && a@[min_idx as int] == a@[k as int],
        decreases a.len() - j
    {
        if a[j] < a[min_idx] {
            min_idx = j;
        }
        j = j + 1;
    }
    min_idx
}

proof fn permut_trans(a: Seq<int>, b: Seq<int>, c: Seq<int>)
    requires
        valid_permut(a, b),
        valid_permut(b, c),
    ensures
        valid_permut(a, c),
{
    assert(a.to_multiset() == b.to_multiset());
    assert(b.to_multiset() == c.to_multiset());
}
// </vc-helpers>

// <vc-spec>
fn lol_sort(a: &mut Vec<int>)
    ensures 
        valid_permut(a@, old(a)@),
        sorted(a@),
// </vc-spec>
// <vc-code>
{
    let ghost original_a = a@;
    let mut i: usize = 0;
    while i < a.len()
        invariant
            a.len() == original_a.len(),
            0 <= i <= a.len(),
            valid_permut(a@, original_a),
            sorted(a@.subrange(0, i as int)),
            forall|j: int, k: int| 0 <= j < i && i <= k < a.len() ==> a@[j] <= a@[k],
        decreases a.len() - i
    {
        let min_idx = find_min_index(a, i);

        let ghost a_before_swap = a@;
        swap(a, i, min_idx);

        proof {
            permut_trans(a@, a_before_swap, original_a);
        }

        i = i + 1;
    }
}
// </vc-code>

}
fn main() {}