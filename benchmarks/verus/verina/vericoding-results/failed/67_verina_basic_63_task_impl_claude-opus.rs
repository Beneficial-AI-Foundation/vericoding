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
{
    /* code modified by LLM (iteration 4): Fixed compilation error - using usize indexing instead of int */
    let n = numbers.len();
    for i in 0..n
        invariant
            forall|k: int, l: int| 
                0 <= k < i as int && 0 <= l < n as int && k != l ==> 
                abs_diff(numbers[k] as int, numbers[l] as int) >= threshold as int
    {
        for j in 0..n
            invariant
                forall|k: int| 
                    0 <= k < j as int && k != i as int ==> 
                    abs_diff(numbers[i as int] as int, numbers[k] as int) >= threshold as int
        {
            if i != j {
                let diff = if numbers[i] >= numbers[j] { 
                    numbers[i] - numbers[j] 
                } else { 
                    numbers[j] - numbers[i] 
                };
                if diff < threshold {
                    return true;
                }
            }
        }
    }
    false
}
// </vc-code>

}
fn main() {}