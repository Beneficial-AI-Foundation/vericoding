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
/* helper modified by LLM (iteration 5): no helpers needed */
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
/* code modified by LLM (iteration 5): Corrected type mismatches for `nat` and `usize` in loop condition and indexing, casting `nat` to `usize` where required for indexing and `usize` to `nat` for `decreases` clause. `b[i]` was also cast to `u32` */
{
    let mut result: Vec<i32> = Vec::new();
    let mut i: nat = 0;

    while (i as usize) < a.len()
        invariant
            a.len() == b.len(),
            result.len() == (i as usize),
            forall|j: int| 0 <= j < i ==> 
                #[trigger] result[j as usize] as int == shift_right_int(a[j as usize] as int, b[j as usize] as nat),
            forall|j: int| 0 <= j < b.len() ==> b[j as usize] < 64,

        decreases (a.len() - (i as usize)) as nat
    {
        result.push(a[i as usize] >> (b[i as usize] as u32));
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}