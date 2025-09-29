use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn reverse(a: &mut Vec<i32>)
    ensures forall|k: int| 0 <= k < old(a).len() ==> a[k] == old(a)[old(a).len() as int - 1 - k]
// </vc-spec>
// <vc-code>
{
    let len = a.len();
    let mut i = 0;
    
    while i < len / 2
        invariant 
            a.len() == len,
            0 <= i <= len / 2,
            forall|k: int| 0 <= k < i ==> a[k] == old(a)[len as int - 1 - k],
            forall|k: int| len as int - i <= k < len ==> a[k] == old(a)[len as int - 1 - k],
            forall|k: int| i <= k < len as int - i ==> a[k] == old(a)[k]
        decreases len / 2 - i
    {
        let temp = a[i];
        let temp2 = a[len - 1 - i];
        a.set(i, temp2);
        a.set(len - 1 - i, temp);
        i += 1;
    }
}
// </vc-code>

fn main() {
}

}