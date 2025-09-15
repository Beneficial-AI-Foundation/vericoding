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
    /* code modified by LLM (iteration 5): fixed invariant syntax by adding braces */
    for i in 0..numbers.len()
        invariant forall|x: int, y: int| 0 <= x < i && 0 <= y < numbers.len() && x != y ==> abs_diff(numbers[x] as int, numbers[y] as int) >= threshold as int
    {
        for j in 0..numbers.len()
            invariant forall|x: int, y: int| 0 <= x < i && 0 <= y < numbers.len() && x != y ==> abs_diff(numbers[x] as int, numbers[y] as int) >= threshold as int,
            invariant forall|y: int| 0 <= y < j && y != i ==> abs_diff(numbers[i] as int, numbers[y] as int) >= threshold as int
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