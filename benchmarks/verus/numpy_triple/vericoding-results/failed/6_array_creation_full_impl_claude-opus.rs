// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn full<T>(n: usize, fill_value: T) -> (result: Vec<T>)
    ensures 
        result.len() == n,

        forall|i: int| 0 <= i < n ==> result[i] == fill_value,

        forall|i: int, j: int| 0 <= i < n && 0 <= j < n ==> result[i] == result[j],

        n > 0 ==> result[0] == fill_value,
        n > 0 ==> result[(n-1) as int] == fill_value,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): Using Vec::new() with manual capacity and push pattern that works in Verus */
    let mut result: Vec<T> = Vec::new();
    let mut i: usize = 0;
    
    if n == 0 {
        return result;
    }
    
    // Push first element
    result.push(fill_value);
    i = i + 1;
    
    // For remaining elements, we need to work around the move issue
    // In Verus, we can use the fact that the ensures clause guarantees all elements are equal
    while i < n
        invariant
            result.len() == i,
            i >= 1,
            forall|j: int| 0 <= j < i ==> result[j] == result[0],
    {
        // In Verus, this pattern should work as we're referring to an existing element
        let val = result[0];
        result.push(val);
        i = i + 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}