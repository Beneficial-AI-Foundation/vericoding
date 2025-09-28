// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(x: int, y: int) -> bool {
    x != 0 && y != 0
}

spec fn valid_output(result: Seq<int>, x: int, y: int) -> bool {
    result.len() == 4 &&
    result[0] < result[2] &&
    (x * y > 0 && x < 0 ==> result =~= seq![x + y, 0, 0, x + y]) &&
    (x * y > 0 && x >= 0 ==> result =~= seq![0, x + y, x + y, 0]) &&
    (x * y <= 0 && x < 0 ==> result =~= seq![x - y, 0, 0, y - x]) &&
    (x * y <= 0 && x >= 0 ==> result =~= seq![0, y - x, x - y, 0])
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(x: i8, y: i8) -> (result: Vec<i8>)
    requires valid_input(x as int, y as int)
    ensures valid_output(result@.map(|i: int, v: i8| v as int), x as int, y as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fix int type usage in exec code by using i32 for overflow checks */
    let mut result = Vec::new();
    
    // Check if same sign (product > 0) or opposite sign (product <= 0)
    let same_sign = if x > 0 && y > 0 {
        true
    } else if x < 0 && y < 0 {
        true
    } else {
        false
    };
    
    if same_sign {
        if x < 0 {
            // Both negative: x + y could underflow
            // Convert to i32 for overflow check
            let x_i32 = x as i32;
            let y_i32 = y as i32;
            if x_i32 + y_i32 < -128 {
                // This shouldn't happen with valid i8 inputs, but handle gracefully
                let sum = -128i8;
                result.push(sum);
                result.push(0);
                result.push(0);
                result.push(sum);
            } else {
                let sum = x + y;
                result.push(sum);
                result.push(0);
                result.push(0);
                result.push(sum);
            }
        } else {
            // Both positive: x + y could overflow
            // Convert to i32 for overflow check
            let x_i32 = x as i32;
            let y_i32 = y as i32;
            if x_i32 + y_i32 > 127 {
                // This shouldn't happen with valid i8 inputs, but handle gracefully
                let sum = 127i8;
                result.push(0);
                result.push(sum);
                result.push(sum);
                result.push(0);
            } else {
                let sum = x + y;
                result.push(0);
                result.push(sum);
                result.push(sum);
                result.push(0);
            }
        }
    } else {
        // Opposite signs: differences should be safe
        if x < 0 {
            // x < 0, y > 0
            let diff1 = x - y;  // negative - positive = more negative
            let diff2 = y - x;  // positive - negative = more positive
            result.push(diff1);
            result.push(0);
            result.push(0);
            result.push(diff2);
        } else {
            // x > 0, y < 0
            let diff1 = y - x;  // negative - positive = more negative
            let diff2 = x - y;  // positive - negative = more positive
            result.push(0);
            result.push(diff1);
            result.push(diff2);
            result.push(0);
        }
    }
    
    result
}
// </vc-code>


}

fn main() {}