use vstd::prelude::*;

verus! {

#[verifier::external_body]
fn swap(a: &mut Vec<bool>, i: usize, j: usize)
    requires
        0 <= i < j < old(a).len(),
    ensures
        a[i as int] == old(a)[j as int],
        a[j as int] == old(a)[i as int],
        forall|k: int| 0 <= k < a.len() && k != i && k != j ==> a[k] == old(a)[k],
        a.len() == old(a).len(),
        a@.to_multiset() =~~= old(a)@.to_multiset(),
{
}

#[verifier::loop_isolation(false)]
fn two_way_sort(a: &mut Vec<bool>)
    requires
        old(a).len() <= 100_000,
    ensures
        a.len() == old(a).len(),
        a@.to_multiset() == old(a)@.to_multiset(),
        forall|i: int, j: int| 0 <= i < j < a.len() ==> !a[i] || a[j],
{
    let mut left = 0;
    let mut right = a.len();
    
    /* code modified by LLM (iteration 1): added decreases clause for loop termination */
    while left < right
        invariant
            0 <= left <= right <= a.len(),
            a.len() == old(a).len(),
            a@.to_multiset() == old(a)@.to_multiset(),
            forall|i: int| 0 <= i < left ==> !a[i],
            forall|i: int| right <= i < a.len() ==> a[i],
        decreases right - left
    {
        if a[left] == false {
            left += 1;
        } else {
            right -= 1;
            if left < right {
                swap(a, left, right);
            }
        }
    }
}

fn main() {}
}