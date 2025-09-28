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
    let mut i: usize = 0;
    while i < a.len()
        invariant
            a.len() == old(a).len(),
            0 <= i as int <= a.len(),
            forall|j: int|
                0 <= j && j < i as int ==> ({
                    if old(a)[j] < 0 { #[trigger] a[j] == 0 } else { #[trigger] a[j] == old(a)[j] }
                }),
            forall|j: int|
                i as int <= j && j < a.len() ==> #[trigger] a[j] == old(a)[j]
        decreases (a.len() - i) as int
    {
        if a[i] < 0 {
            a[i] = 0;
        } else {
            // leave as is
        }
        i += 1;
    }
}
// </vc-code>

fn main() {
}

}