// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): No helpers provided */
// </vc-helpers>

// <vc-spec>
fn trap_rain_water(height: &Vec<usize>) -> (result: usize)
    requires height.len() >= 0,
    ensures result >= 0,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): Fixed invariant curly braces. */
{
    let n = height.len();
    if n == 0 {
        return 0;
    }

    let mut left_max: Vec<usize> = Vec::new();
    let mut current_max: usize = 0;

    let mut i = 0;
    while i < n
        invariant i <= n,
        invariant left_max.len() == i
    {
        left_max.push(current_max);
        current_max = max_spec(current_max as int, height[i] as int) as usize;
        i = i + 1;
    }

    let mut right_max: Vec<usize> = Vec::new();
    current_max = 0;

    let mut i = n;
    while i > 0
        invariant i <= n,
        invariant right_max.len() == n - i
    {
        i = i - 1;
        right_max.insert(0,current_max);
        current_max = max_spec(current_max as int, height[i] as int) as usize;
    }

    let mut total_water: usize = 0;
    let mut i = 0;
    while i < n
        invariant i <= n,
        invariant total_water >= 0
    {
        let min_boundary = min_spec(left_max[i] as int, right_max[i] as int) as usize;
        if height[i] < min_boundary {
            total_water = total_water + (min_boundary - height[i]);
        }
        i = i + 1;
    }
    total_water
}
// </vc-code>

}
fn main() {}