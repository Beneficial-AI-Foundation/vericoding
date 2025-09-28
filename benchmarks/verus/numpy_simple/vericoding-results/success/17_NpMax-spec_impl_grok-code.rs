// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn max(a: Vec<i8>) -> (result: i8)
    requires a.len() > 0,
    ensures 
        exists|i: int| 0 <= i < a@.len() && result as int == a@[i],
        forall|i: int| 0 <= i < a@.len() ==> a@[i] <= result as int
// </vc-spec>
// <vc-code>
{
    let mut max_val = a[0];
    let mut i = 1;
    while i < a.len()
        invariant
            i <= a.len(),
            exists|j: int| 0 <= j < i && max_val as int == a@[j],
            forall|j: int| 0 <= j < i ==> a@[j] <= max_val as int,
        decreases a.len() - i
    {
        if a[i] > max_val {
            max_val = a[i];
        }
        i += 1;
    }
    return max_val;
}
// </vc-code>


}
fn main() {}