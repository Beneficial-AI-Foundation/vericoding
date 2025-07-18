use vstd::prelude::*;

verus! {

//IMPL swap
fn swap(a: &mut Vec<bool>, i: usize, j: usize)
    requires
        /* code modified by LLM (iteration 3): Fixed old() reference in requires clause */
        0 <= i && i < j && j < old(a).len(),
    ensures
        /* code modified by LLM (iteration 2): Fixed placement of ensures clause */
        a[i as int] == old(a)[j as int],
        a[j as int] == old(a)[i as int],
        forall|k: int| 0 <= k < a.len() && k != i && k != j ==> a[k] == old(a)[k],
        a.len() == old(a).len(),
        a@.to_multiset() =~~= old(a)@.to_multiset(),
{
    /* code modified by LLM (iteration 2): Implemented swap logic */
    let temp = a[i];
    a.set(i, a[j]);
    a.set(j, temp);
}

//IMPL two_way_sort
#[verifier::loop_isolation(false)]
fn two_way_sort(a: &mut Vec<bool>)
    requires
        /* code modified by LLM (iteration 2): Fixed placement of requires clause */
        a.len() <= 100_000,
    ensures
        /* code modified by LLM (iteration 2): Fixed placement of ensures clause */
        a.len() == old(a).len(),
        a@.to_multiset() == old(a)@.to_multiset(),
        forall|i: int, j: int| 0 <= i && i < j && j < a.len() ==> !a[i] || a[j],
{
    /* code modified by LLM (iteration 2): Implemented two-way sort algorithm */
    let mut left = 0;
    let mut right = a.len();
    
    while left < right
        invariant
            0 <= left <= right <= a.len(),
            a.len() == old(a).len(),
            a@.to_multiset() == old(a)@.to_multiset(),
            forall|i: int| 0 <= i < left ==> !a[i],
            forall|i: int| right <= i < a.len() ==> a[i],
    {
        if !a[left] {
            left += 1;
        } else if a[right - 1] {
            right -= 1;
        } else {
            swap(a, left, right - 1);
            left += 1;
            right -= 1;
        }
    }
}

fn main() {}
}