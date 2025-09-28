// <vc-preamble>
use vstd::prelude::*;
use vstd::arithmetic::power2::pow2;

verus! {
spec fn shift_right_int(x: int, n: nat) -> int {
    if x >= 0 {
        x / (pow2(n) as int)
    } else {
        -((((-x) - 1) / (pow2(n) as int)) + 1)
    }
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn right_shift(a: Vec<i32>, b: Vec<u32>) -> (result: Vec<i32>)
    requires 
        a.len() == b.len(),
        forall|i: int| 0 <= i < b.len() ==> b[i] < 64,
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> 
            result[i] as int == shift_right_int(a[i] as int, b[i] as nat),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Added decreases clause to while loop */
    let mut result = Vec::new();
    let n = a.len();
    let mut i = 0;
    while i < n
        invariant
            i <= n,
            n == a.len(),
            n == b.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] as int == shift_right_int(a[j] as int, b[j] as nat),
            forall|j: int| 0 <= j < b.len() ==> b[j] < 64,
        decreases n - i
    {
        let val = a[i] >> b[i];
        result.push(val);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}