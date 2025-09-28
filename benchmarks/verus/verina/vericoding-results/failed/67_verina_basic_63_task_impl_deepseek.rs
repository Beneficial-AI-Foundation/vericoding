// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn abs_diff(a: int, b: int) -> int {
    if a >= b { a - b } else { b - a }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed integer conversion for executable code */
fn abs_diff_exec(a: i32, b: i32) -> i32 {
    if a >= b { a - b } else { b - a }
}
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
/* code modified by LLM (iteration 5): Fixed type casting and integer comparisons */
{
    let len = numbers.len();
    let mut i: usize = 0;
    
    while i < len
        invariant
            0 <= i <= len,
            forall|k: int, l: int| 0 <= k < i && 0 <= l < len && k != l ==> 
                abs_diff(numbers[k] as int, numbers[l] as int) >= threshold as int,
        decreases len - i
    {
        let mut j: usize = i + 1;
        
        while j < len
            invariant
                i < j <= len,
                forall|l: int| i < l < j ==> 
                    abs_diff(numbers[i] as int, numbers[l] as int) >= threshold as int,
            decreases len - j
        {
            let diff_exec = abs_diff_exec(numbers[i], numbers[j]);
            if (diff_exec as int) < threshold as int {
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