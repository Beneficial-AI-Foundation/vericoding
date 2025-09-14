// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

proof fn partition_lemma(s: Seq<bool>, left: nat, right: nat) -> (partitioned: Seq<bool>)
    ensures
        partitioned.len() == s.len(),
        partitioned.to_multiset() == s.to_multiset(),
        forall|i: int| 0 <= i < left as int ==> !partitioned[i],
        forall|j: int| right as int <= j < partitioned.len() as int ==> partitioned[j],
{
    if left >= right {
        s
    } else {
        let mid = (left as int + (right as int - left as int) / 2) as nat;
        let s_left = partition_lemma(s, left, mid);
        partition_lemma(s_left, mid, right)
    }
}

fn swap_helper(a: &mut Vec<bool>, i: usize, j: usize)
    requires
        i < old(a).len(),
        j < old(a).len(),
    ensures
        a.len() == old(a).len(),
        a@.to_multiset() == old(a)@.to_multiset(),
        a@.index(i) == old(a)@.index(j),
        a@.index(j) == old(a)@.index(i),
        forall|k: int| 0 <= k < a@.len() && k != i as int && k != j as int ==> a@.index(k) == old(a)@.index(k),
{
    let temp = a[i];
    a[i] = a[j];
    a[j] = temp;
}

// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn two_way_sort(a: &mut Vec<bool>)
    requires
        old(a).len() <= 100_000,
    ensures
        a.len() == old(a).len(),
        a@.to_multiset() == old(a)@.to_multiset(),
        forall|i: int, j: int| 0 <= i < j < a.len() ==> !a[i] || a[j],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed int/nat casting issues */
    let len = a.len();
    let mut i: usize = 0;
    let mut j: usize = len;
    
    while i < j
        invariant
            0 <= i <= j <= len,
            a@.to_multiset() == old(a)@.to_multiset(),
            forall|k: int| 0 <= k < i as int ==> !a@[k],
            forall|k: int| j as int <= k < len as int ==> a@[k],
    {
        if a@[i as int] {
            j -= 1;
            swap_helper(a, i, j);
        } else {
            i += 1;
        }
    }
}
// </vc-code>

}
fn main() {}