// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): added helper functions for min operation */
fn min_usize(a: usize, b: usize) -> usize {
    if a < b { a } else { b }
}
// </vc-helpers>

// <vc-spec>
fn trap_rain_water(height: &Vec<usize>) -> (result: usize)
    requires height.len() >= 0,
    ensures result >= 0,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): added decreases clauses to all loops */
    if height.len() == 0 {
        return 0;
    }
    
    let mut left_max: Vec<usize> = Vec::new();
    let mut right_max: Vec<usize> = Vec::new();
    
    // Initialize vectors
    let mut i = 0;
    while i < height.len()
        invariant left_max.len() == i,
                 right_max.len() == i,
                 i <= height.len()
        decreases height.len() - i
    {
        left_max.push(0);
        right_max.push(0);
        i += 1;
    }
    
    // Fill left_max
    left_max.set(0, height[0]);
    i = 1;
    while i < height.len()
        invariant 1 <= i <= height.len(),
                 left_max.len() == height.len(),
                 right_max.len() == height.len()
        decreases height.len() - i
    {
        let prev_max = left_max[i - 1];
        let curr_height = height[i];
        if curr_height > prev_max {
            left_max.set(i, curr_height);
        } else {
            left_max.set(i, prev_max);
        }
        i += 1;
    }
    
    // Fill right_max
    right_max.set(height.len() - 1, height[height.len() - 1]);
    i = height.len() - 1;
    while i > 0
        invariant 0 <= i < height.len(),
                 left_max.len() == height.len(),
                 right_max.len() == height.len()
        decreases i
    {
        let next_max = right_max[i];
        let curr_height = height[i - 1];
        if curr_height > next_max {
            right_max.set(i - 1, curr_height);
        } else {
            right_max.set(i - 1, next_max);
        }
        i -= 1;
    }
    
    // Calculate trapped water
    let mut water = 0;
    i = 0;
    while i < height.len()
        invariant i <= height.len(),
                 left_max.len() == height.len(),
                 right_max.len() == height.len()
        decreases height.len() - i
    {
        let left = left_max[i];
        let right = right_max[i];
        let min_height = min_usize(left, right);
        let curr_height = height[i];
        
        if min_height > curr_height {
            water += min_height - curr_height;
        }
        i += 1;
    }
    
    water
}
// </vc-code>

}
fn main() {}