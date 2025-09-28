// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn sign(a: Vec<i32>) -> (result: Vec<i32>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> {
            (a[i] > 0 ==> result[i] == 1) &&
            (a[i] == 0 ==> result[i] == 0) &&
            (a[i] < 0 ==> result[i] == -1)
        }
// </vc-spec>
// <vc-code>
{/* code modified by LLM (iteration 2): added decreases clause for the while loop */
    let mut result = Vec::new();
    let mut i = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() == i,
            forall|k: int| 0 <= k < i ==> (
                (a[k] > 0 ==> result[k] == 1) &&
                (a[k] == 0 ==> result[k] == 0) &&
                (a[k] < 0 ==> result[k] == -1)
            )
        decreases a.len() - i
    {
        if a[i] > 0 {
            result.push(1);
        } else if a[i] < 0 {
            result.push(-1);
        } else {
            result.push(0);
        }
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}