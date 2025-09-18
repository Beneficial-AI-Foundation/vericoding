// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): added overflow checking helper */
fn safe_add(a: usize, b: usize) -> (result: usize)
    requires a + b <= usize::MAX,
    ensures result == a + b,
{
    a + b
}
// </vc-helpers>

// <vc-spec>
fn trap_rain_water(height: &Vec<usize>) -> (result: usize)
    requires height.len() >= 0,
    ensures result >= 0,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): added overflow checking for trapped water accumulation */
    if height.len() <= 2 {
        return 0;
    }
    
    let mut left_max = Vec::new();
    let mut right_max = Vec::new();
    let mut trapped = 0usize;
    
    let mut i = 0;
    while i < height.len()
        invariant
            i <= height.len(),
            left_max.len() == i,
            right_max.len() == i,
        decreases height.len() - i
    {
        left_max.push(0usize);
        right_max.push(0usize);
        i += 1;
    }
    
    left_max.set(0, height[0]);
    i = 1;
    while i < height.len()
        invariant
            1 <= i <= height.len(),
            left_max.len() == height.len(),
            i > 0,
            left_max[0] == height[0],
        decreases height.len() - i
    {
        if height[i] > left_max[i - 1] {
            left_max.set(i, height[i]);
        } else {
            left_max.set(i, left_max[i - 1]);
        }
        i += 1;
    }
    
    right_max.set(height.len() - 1, height[height.len() - 1]);
    i = height.len() - 1;
    while i > 0
        invariant
            i < height.len(),
            right_max.len() == height.len(),
            right_max[height.len() - 1] == height[height.len() - 1],
        decreases i
    {
        if i < height.len() - 1 {
            if height[i] > right_max[i + 1] {
                right_max.set(i, height[i]);
            } else {
                right_max.set(i, right_max[i + 1]);
            }
        }
        i -= 1;
    }
    
    i = 0;
    while i < height.len()
        invariant
            i <= height.len(),
            left_max.len() == height.len(),
            right_max.len() == height.len(),
            trapped <= usize::MAX,
        decreases height.len() - i
    {
        let water_level = if left_max[i] < right_max[i] { left_max[i] } else { right_max[i] };
        if water_level > height[i] {
            let water_amount = water_level - height[i];
            if trapped <= usize::MAX - water_amount {
                trapped = safe_add(trapped, water_amount);
            }
        }
        i += 1;
    }
    
    trapped
}
// </vc-code>

}
fn main() {}