use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn zap_negatives(a: &mut Vec<i32>)
    ensures 
        a.len() == old(a).len(),
        forall|i: int| 0 <= i < a.len() ==> 
            if old(a)[i] < 0 { a[i] == 0 } 
            else { a[i] == old(a)[i] }
// </vc-spec>
// <vc-code>
{
    let old_a = a.clone();
    let mut i = 0;
    while i < a.len()
        invariant
            a.len() == old_a.len(),
            0 <= i <= a.len(),
            forall|k: int| 0 <= k < i ==>
                if old_a[k] < 0 { a[k] == 0 }
                else { a[k] == old_a[k] },
            forall|k: int| i <= k < a.len() ==>
                a[k] == old_a[k],
        decreases a.len() - i,
    {
        if a[i] < 0 {
            a.set(i, 0);
        }
        i = i + 1;
    }
}
// </vc-code>

fn main() {
}

}