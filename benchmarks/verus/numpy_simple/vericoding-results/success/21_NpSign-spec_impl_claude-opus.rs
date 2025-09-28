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
{
    /* code modified by LLM (iteration 2): Added decreases clause to while loop */
    let mut result = Vec::new();
    let mut i = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> {
                (a[j] > 0 ==> result[j] == 1) &&
                (a[j] == 0 ==> result[j] == 0) &&
                (a[j] < 0 ==> result[j] == -1)
            },
        decreases a.len() - i
    {
        let val = a[i];
        if val > 0 {
            result.push(1);
        } else if val == 0 {
            result.push(0);
        } else {
            result.push(-1);
        }
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}