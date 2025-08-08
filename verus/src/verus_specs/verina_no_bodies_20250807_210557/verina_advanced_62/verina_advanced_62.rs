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
    return 0;  // TODO: Remove this line and implement the function body
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
    // TODO: Remove this comment and implement the function body
}