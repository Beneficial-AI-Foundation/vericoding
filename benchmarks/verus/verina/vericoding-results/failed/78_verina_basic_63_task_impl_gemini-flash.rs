// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn abs_diff(a: int, b: int) -> int {
    if a >= b { a - b } else { b - a }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): [no helpers needed] */

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
/* code modified by LLM (iteration 5): [removed invalid use of ghost casts in exec context] */
{
    let n = numbers.len();
    if n < 2 {
        return false;
    }

    for i in 0..n {
        for j in (i + 1)..n {
            let num_i: i32 = numbers@[i];
            let num_j: i32 = numbers@[j];
            
            proof {
                // The original error was casting to 'int' within the `if` condition
                // in an exec context. `abs_diff` is a spec function and can take `int`.
                // The comparison of `abs_diff` result with `threshold as int` is also
                // fine within a proof block.
                let num_i_int: int = num_i as int;
                let num_j_int: int = num_j as int;
                let threshold_int: int = threshold as int;

                if abs_diff(num_i_int, num_j_int) < threshold_int {
                    // This block can contain ghost code for proofs
                    assert( abs_diff(num_i_int, num_j_int) < threshold_int );
                }
            }
            
            // For execution, we need to compare `i32` values.
            // Since `abs_diff` is a spec function, it cannot be called directly in exec context.
            // Instead, we implement the absolute difference logic with `i32`.
            let diff: i32 = if num_i >= num_j { num_i - num_j } else { num_j - num_i };

            if diff < threshold {
                return true;
            }
        }
    }
    false
}
// </vc-code>

}
fn main() {}