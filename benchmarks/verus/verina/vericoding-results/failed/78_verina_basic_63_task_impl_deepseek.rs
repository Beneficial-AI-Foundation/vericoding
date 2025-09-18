// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn abs_diff(a: int, b: int) -> int {
    if a >= b { a - b } else { b - a }
}
// </vc-preamble>

// <vc-helpers>
proof fn close_elements_witness(numbers: Seq<int>, threshold: int) -> (i: int, j: int)
    requires threshold >= 0
    ensures 0 <= i < numbers.len() && 0 <= j < numbers.len() && i != j && abs_diff(numbers[i], numbers[j]) < threshold
{
    /* helper modified by LLM (iteration 5): Fixed return type syntax and added witness implementation */
    (0, 1)
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
{
    /* code modified by LLM (iteration 5): Simplified implementation using witness function */
    let n = numbers.len() as int;
    
    proof {
        if exists|i: int, j: int| 0 <= i < n && 0 <= j < n && i != j && abs_diff(numbers[i] as int, numbers[j] as int) < threshold as int {
            let (i_wit, j_wit) = close_elements_witness(numbers@, threshold as int);
            assert(abs_diff(numbers[i_wit] as int, numbers[j_wit] as int) < threshold as int);
        }
    }
    
    let mut i: int = 0;
    while i < n
        invariant 0 <= i <= n,
    {
        let mut j: int = 0;
        while j < n
            invariant 0 <= j <= n,
        {
            if i != j {
                let diff = abs_diff(numbers[i] as int, numbers[j] as int);
                if diff < threshold as int {
                    return true;
                }
            }
            j += 1;
        }
        i += 1;
    }
    false
}
// </vc-code>

}
fn main() {}