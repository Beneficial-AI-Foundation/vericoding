// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Rename helper to avoid confusion, return i32 */
spec fn calculate_product(a: i32, b: i32) -> i32 {
    (a as int * b as int) as i32
}
// </vc-helpers>

// <vc-spec>
fn multiply(a: i32, b: i32) -> (result: i32)
    ensures result == a * b,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Correct the loop calculation and invariants */
{
    let mut res: i32 = 0;
    let mut i: i32 = 0;

    if b == 0 {
        return 0i32;
    }

    if b > 0 {
        while i < b
            invariant
                0 <= i <= b,
                res == calculate_product(a, i),
                calculate_product(a, b) == calculate_product(a, i) + calculate_product(a, b - i)
            decreases b - i
        {
            res = res + a;
            i = i + 1;
        }
    } else { // b < 0
        while i > b
            invariant
                b <= i <= 0,
                res == calculate_product(a, i),
                calculate_product(a, b) == calculate_product(a, i) + calculate_product(a, b - i)
            decreases i - b
        {
            res = res + a;
            i = i - 1;
        }
    }
    res
}
// </vc-code>

}
fn main() {}