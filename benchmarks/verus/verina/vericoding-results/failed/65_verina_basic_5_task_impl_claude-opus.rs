// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn multiply(a: i32, b: i32) -> (result: i32)
    ensures result == a * b,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Using wrapping arithmetic to handle overflow cases */
    if a == 0 || b == 0 {
        return 0;
    }
    
    // Handle special case where b is i32::MIN to avoid overflow on negation
    if b == i32::MIN {
        if a == 1 {
            return i32::MIN;
        } else if a == -1 {
            // -1 * i32::MIN would overflow, but mathematically equals i32::MAX + 1
            // In wrapping arithmetic, this gives i32::MIN
            return i32::MIN.wrapping_neg();
        } else {
            // For other values, use wrapping multiplication
            return a.wrapping_mul(b);
        }
    }
    
    let mut result: i32 = 0;
    let mut i: i32 = 0;
    
    // Safe to negate b since we handled i32::MIN case
    let abs_b = if b >= 0 { b } else { -b };
    let need_negate = b < 0;
    
    while i < abs_b
        invariant
            i >= 0,
            i <= abs_b,
            result == a.wrapping_mul(i),
        decreases abs_b - i,
    {
        result = result.wrapping_add(a);
        i = i + 1;
    }
    
    // Apply sign if b was negative
    if need_negate {
        result = result.wrapping_neg();
    }
    
    result
}
// </vc-code>

}
fn main() {}