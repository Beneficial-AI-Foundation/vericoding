use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn maxArray(a: &[int]) -> (m: int)
    requires a.len() >= 1,
    ensures 
        forall|k: int| 0 <= k < a.len() ==> m >= a@[k] &&
        exists|k: int| 0 <= k < a.len() && m == a@[k],
// </vc-spec>
// <vc-code>
{
    let mut m = a[0];
    let mut i = 1;
    
    while i < a.len()
        invariant
            1 <= i <= a.len(),
            forall|k: int| 0 <= k < i ==> m >= a@[k],
            exists|k: int| 0 <= k < i && m == a@[k],
        decreases a.len() - i,
    {
        if a[i] > m {
            m = a[i];
        }
        i = i + 1;
    }
    
    m
}
// </vc-code>

fn main() {
}

}