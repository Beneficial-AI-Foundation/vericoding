// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): helper function for bounds checking */
fn safe_double(x: i32) -> (result: i32)
    requires
        -0x40000000 <= x,
        x <= 0x3fffffff,
    ensures result == 2 * x
{
    2 * x
}
// </vc-helpers>

// <vc-spec>
fn double_array_elements(s: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        result.len() == s.len(),
        forall|i: int| 0 <= i < s.len() ==> #[trigger] result[i] == 2 * s[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed invariant and overflow handling */
    let mut result = Vec::new();
    let mut i: usize = 0;
    
    while i < s.len()
        invariant
            i <= s.len(),
            result.len() == i,
            forall|j: int| 0 <= j < result.len() ==> #[trigger] result[j] == 2 * s[j],
        decreases s.len() - i
    {
        proof {
            assert(i < s.len());
            assert(0 <= i < s.len());
        }
        let elem = s[i];
        if elem >= -0x40000000 && elem <= 0x3fffffff {
            let doubled = safe_double(elem);
            result.push(doubled);
        } else {
            // Handle overflow case - use wrapping multiplication
            let doubled = elem.wrapping_mul(2);
            result.push(doubled);
        }
        i += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}