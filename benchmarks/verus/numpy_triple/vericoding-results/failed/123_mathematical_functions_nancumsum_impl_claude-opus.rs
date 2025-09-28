// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn nancumsum(a: Vec<i8>) -> (result: Vec<i8>)
    ensures
        result.len() == a.len(),
        a.len() > 0 ==> (result[0] as int == a[0] as int),
        forall|i: int| 0 < i < result.len() ==> result[i] as int == result[i-1] as int + a[i] as int,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed int type usage - using i32 for arithmetic instead of int */
    let mut result = Vec::new();
    if a.len() == 0 {
        return result;
    }
    
    result.push(a[0]);
    let mut i: usize = 1;
    
    while i < a.len()
        invariant
            i >= 1,
            i <= a.len(),
            result.len() == i,
            result[0] as int == a[0] as int,
            forall|j: int| 0 < j < i ==> result[j] as int == result[j-1] as int + a[j] as int,
        decreases a.len() - i
    {
        let prev = result[i - 1];
        let curr = a[i];
        
        // Check for overflow before addition
        if prev > 0 && curr > 0 && prev > (127 - curr) {
            // Would overflow, but we still need to maintain the specification
            let sum = ((prev as i32 + curr as i32) % 256) as i8;
            result.push(sum);
        } else if prev < 0 && curr < 0 && prev < (-128 - curr) {
            // Would underflow, but we still need to maintain the specification  
            let sum = ((prev as i32 + curr as i32) % 256) as i8;
            result.push(sum);
        } else {
            // Safe to add without overflow
            let sum = prev + curr;
            result.push(sum);
        }
        
        // Assert to help verify the invariant
        assert(result.len() == i + 1);
        assert(result[i] as int == result[i-1] as int + a[i] as int);
        
        i = i + 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}