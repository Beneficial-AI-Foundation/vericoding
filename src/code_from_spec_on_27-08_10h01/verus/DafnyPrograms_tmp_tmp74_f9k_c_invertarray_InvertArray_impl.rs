use vstd::prelude::*;

verus! {

/**
  Inverts an array of ints.
 */

// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn invert_array(a: &mut Vec<i32>)
    ensures
        a.len() == old(a).len(),
        forall|i: int| 0 <= i < a.len() ==> a[i] == old(a)[a.len() - 1 - i],
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    let len = a.len();
    let mut i = 0;
    
    while i < len / 2
        invariant
            a.len() == len,
            len == old(a).len(),
            forall|j: int| 0 <= j < i ==> a[j] == old(a)[len - 1 - j],
            forall|j: int| 0 <= j < i ==> a[len - 1 - j] == old(a)[j],
            forall|j: int| i <= j < len - i ==> a[j] == old(a)[j],
        decreases len / 2 - i
    {
        let temp = a[i];
        let other_temp = a[len - 1 - i];
        a.set(i, other_temp);
        a.set(len - 1 - i, temp);
        i += 1;
    }
}
// </vc-code>

fn main() {
}

}