// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn trap_rain_water(height: &Vec<usize>) -> (result: usize)
    requires height.len() >= 0,
    ensures result >= 0,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): fixed indexing syntax from '@[' to '[' to access Vec elements */
    let n = height.len();
    if n <= 1 {
        return 0;
    }
    let mut total = 0;
    for i in 0..n {
        if i == 0 || i == n-1 {
            continue;
        }
        let mut left_max = height[0];
        for j in 1..i {
            left_max = left_max.max(height[j]);
        }
        let mut right_max = height[n-1];
        for j in i+1..n {
            right_max = right_max.max(height[j]);
        }
        let min_max = left_max.min(right_max);
        if min_max > height[i] {
            total = total + min_max - height[i];
        }
    }
    total
}
// </vc-code>

}
fn main() {}