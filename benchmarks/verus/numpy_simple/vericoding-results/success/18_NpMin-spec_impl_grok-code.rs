// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn min(a: Vec<i8>) -> (result: i8)
    requires a.len() > 0,
    ensures 
        exists|i: int| 0 <= i < a@.len() && result as int == a@[i],
        forall|i: int| 0 <= i < a@.len() ==> result as int <= a@[i]
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): added decreases clause to the while loop */
    if a.len() == 1 {
        return a[0];
    } else {
        let mut min_val = a[0];
        let mut i = 1;
        while i < a.len()
            invariant
                1 <= i <= a.len(),
                exists|k: int| 0 <= k < i && min_val as int == a@[k],
                forall|j: int| 0 <= j < i ==> min_val as int <= a@[j],
            decreases a.len() - i
        {
            if a[i] < min_val {
                min_val = a[i];
            }
            i += 1;
        }
        return min_val;
    }
}
// </vc-code>


}
fn main() {}