// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn abs_diff(a: int, b: int) -> int {
    if a >= b { a - b } else { b - a }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Removed unnecessary proof helper definition. */

// </vc-helpers>

// <vc-spec>
fn has_close_elements(numbers: &Vec<i32>, threshold: i32) -> (result: bool)
    requires threshold >= 0,
    ensures
        !result <==> (forall|i: int, j: int| 
            0 <= i < numbers.len() && 0 <= j < numbers.len() && i != j ==> 
            abs_diff(numbers[i] as int, numbers[j] as int) >= threshold as int),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Corrected type casting in the `abs_diff` comparison to use `int` consistently for `numbers[i]` and `numbers[j]` and `threshold`. */
{
    let n = numbers.len();
    if n < 2 {
        return false;
    }

    let mut i = 0;
    while i < n
        invariant
            0 <= i,
            i <= n

    {
        let mut j = i + 1;
        while j < n
            invariant
                0 <= i,
                i < j,
                j <= n
            decreases (n - j) as int
        {
            if abs_diff(numbers[i] as int, numbers[j] as int) < threshold as int {
                return true;
            }
            j = j + 1;
        }
        i = i + 1;
    }
    false
}
// </vc-code>

}
fn main() {}