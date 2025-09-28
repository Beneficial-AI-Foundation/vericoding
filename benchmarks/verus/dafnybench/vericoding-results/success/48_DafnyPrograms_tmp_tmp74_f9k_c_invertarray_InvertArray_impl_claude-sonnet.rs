use vstd::prelude::*;

verus! {

/**
  Inverts an array of ints.
 */

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn invert_array(a: &mut Vec<i32>)
    ensures
        a.len() == old(a).len(),
        forall|i: int| 0 <= i < a.len() ==> a[i] == old(a)[a.len() - 1 - i],
// </vc-spec>
// <vc-code>
{
    let n = a.len();
    let mut i = 0;
    
    while i < n / 2
        invariant
            0 <= i <= n / 2,
            a.len() == n,
            forall|j: int| 0 <= j < i ==> a[j] == old(a)[n - 1 - j],
            forall|j: int| 0 <= j < i ==> a[n - 1 - j] == old(a)[j],
            forall|j: int| i <= j < n - i ==> a[j] == old(a)[j],
        decreases n / 2 - i,
    {
        let temp = a[i];
        let other_temp = a[n - 1 - i];
        a.set(i, other_temp);
        a.set(n - 1 - i, temp);
        i += 1;
    }
}
// </vc-code>

fn main() {
}

}