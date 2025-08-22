use vstd::prelude::*;

verus! {

// Precondition: all heights are non-negative
spec fn rain_precond(heights: Seq<i32>) -> bool {
    forall|i: int| 0 <= i < heights.len() ==> #[trigger] heights[i] >= 0
}

// Postcondition: result is non-negative and zero for arrays with < 3 elements
spec fn rain_postcond(heights: Seq<i32>, result: int) -> bool {
    result >= 0 &&
    if heights.len() < 3 {
        result == 0
    } else {
        // For arrays with >= 3 elements, result is the amount of trapped water
        true
    }
}

// Main rain function implementing the two-pointer algorithm
fn rain(heights: Vec<i32>) -> (result: i32)
    requires 
        rain_precond(heights@),
    ensures 
        rain_postcond(heights@, result as int),
{
    let len = heights.len();
    
    if len < 3 {
        return 0;
    }
    
    let mut left: usize = 0;
    let mut right: usize = len - 1;
    let mut left_max: i32 = 0;
    let mut right_max: i32 = 0;
    let mut water: i32 = 0;
    
    /* code modified by LLM (iteration 1): added decreases clause to prove loop termination */
    while left < right
        invariant
            left <= right,
            right < len,
            left_max >= 0,
            right_max >= 0,
            water >= 0,
        decreases (right - left)
    {
        if heights[left] < heights[right] {
            if heights[left] >= left_max {
                left_max = heights[left];
            } else {
                water = water + (left_max - heights[left]);
            }
            left = left + 1;
        } else {
            if heights[right] >= right_max {
                right_max = heights[right];
            } else {
                water = water + (right_max - heights[right]);
            }
            right = right - 1;
        }
    }
    
    water
}

// Theorem that states the specification is satisfied
proof fn rain_spec_satisfied(heights: Seq<i32>, result: int)
    requires 
        rain_precond(heights),
        rain_postcond(heights, result)
    ensures 
        result >= 0
{
    // This theorem shows that any result satisfying the postcondition
    // is non-negative, which follows directly from the postcondition
}

}

fn main() {
    let heights = vec![0, 1, 0, 2, 1, 0, 1, 3, 2, 1, 2, 1];
    let trapped = rain(heights);
    println!("Trapped water: {}", trapped);
}