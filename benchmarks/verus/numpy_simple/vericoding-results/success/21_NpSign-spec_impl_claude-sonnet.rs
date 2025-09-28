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
    let mut result = Vec::new();
    for i in 0..a.len()
        invariant
            result.len() == i,
            forall|j: int| 0 <= j < i ==> {
                (a[j] > 0 ==> result[j] == 1) &&
                (a[j] == 0 ==> result[j] == 0) &&
                (a[j] < 0 ==> result[j] == -1)
            },
    {
        let sign_val = if a[i] > 0 {
            1
        } else if a[i] == 0 {
            0
        } else {
            -1
        };
        result.push(sign_val);
    }
    result
}
// </vc-code>


}
fn main() {}