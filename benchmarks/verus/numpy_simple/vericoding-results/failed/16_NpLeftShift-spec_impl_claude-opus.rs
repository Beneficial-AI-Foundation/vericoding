// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
spec fn shift_left_int(x: int, shift: nat) -> int;

fn left_shift(a: Vec<i32>, b: Vec<u32>) -> (result: Vec<i32>)
    requires 
        a.len() == b.len(),
        forall|i: int| 0 <= i < b.len() ==> b[i] < 64,
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == shift_left_int(a[i] as int, b[i] as nat),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Added decreases clause to fix loop verification error */
    let mut result = Vec::new();
    let mut i = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            a.len() == b.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == shift_left_int(a[j] as int, b[j] as nat),
            forall|j: int| 0 <= j < b.len() ==> b[j] < 64,
        decreases a.len() - i
    {
        let shifted = if b[i] < 32 {
            a[i] << b[i]
        } else {
            if a[i] >= 0 {
                0
            } else {
                -1
            }
        };
        result.push(shifted);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}