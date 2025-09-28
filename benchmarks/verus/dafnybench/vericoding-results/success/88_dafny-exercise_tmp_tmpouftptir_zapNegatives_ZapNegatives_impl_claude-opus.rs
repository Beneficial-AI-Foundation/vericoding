use vstd::prelude::*;

verus! {

// <vc-helpers>
// No additional helpers needed for this implementation
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
    let mut i: usize = 0;
    while i < a.len()
        invariant
            a.len() == old(a).len(),
            0 <= i <= a.len(),
            forall|j: int| 0 <= j < i ==> 
                if old(a)[j] < 0 { a[j] == 0 } 
                else { a[j] == old(a)[j] },
            forall|j: int| i <= j < a.len() ==> 
                a[j] == old(a)[j],
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