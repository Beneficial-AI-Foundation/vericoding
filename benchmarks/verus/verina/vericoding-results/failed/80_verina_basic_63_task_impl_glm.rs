// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn abs_diff(a: int, b: int) -> int {
    if a >= b { a - b } else { b - a }
}
// </vc-preamble>

// <vc-helpers>

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
/* code modified by LLM (iteration 4): fixed invariant syntax by adding curly braces around quantifiers */
{
    let n = numbers.len();
    for i in 0..n
        invariant { forall |k: int, l: int| 0 <= k < l < i ==> abs_diff(numbers[k] as int, numbers[l] as int) >= threshold as int }
    {
        for j in (i+1)..n
            invariant { forall |k: int, l: int| 0 <= k < l < i ==> abs_diff(numbers[k] as int, numbers[l] as int) >= threshold as int }
            invariant { forall |l: int| i+1 <= l < j ==> abs_diff(numbers[i] as int, numbers[l] as int) >= threshold as int }
        {
            if abs_diff(numbers[i] as int, numbers[j] as int) < threshold as int {
                return true;
            }
        }
    }
    false
}
// </vc-code>

}
fn main() {}