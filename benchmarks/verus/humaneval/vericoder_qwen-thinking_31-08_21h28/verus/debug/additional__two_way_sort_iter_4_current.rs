use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn two_way_sort(a: &mut Vec<bool>)
    // pre-conditions-start
    requires
        old(a).len() <= 100_000,
    // pre-conditions-end
    // post-conditions-start
    ensures
        a.len() == old(a).len(),
        a@.to_multiset() == old(a)@.to_multiset(),
        forall|i: int, j: int| 0 <= i < j < a.len() ==> !a[i] || a[j],
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let n = (a.len() as int);
    let mut left: int = 0;
    let mut right: int = n - 1;
    while left <= right
        invariant 0 <= left && left <= n && 0 <= right && right < n
        invariant (forall|i: int| 0 <= i < left ==> a[i] == false) && (forall|i: int| right < i && i < n ==> a[i] == true)
    {
        if a[left] == false {
            left += 1;
        } else if a[right] == true {
            right -= 1;
        } else {
            let temp = a[left];
            a[left] = a[right];
            a[right] = temp;
            left += 1;
            right -= 1;
        }
    }
}
// </vc-code>

fn main() {}
}