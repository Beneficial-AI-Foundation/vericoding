// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn numpy_bitwise_not(x: Vec<i8>) -> (result: Vec<i8>)
    ensures 
        result.len() == x.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] as int == -(x[i] as int + 1)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): handle bitwise NOT with overflow checking */
    let mut result = Vec::new();
    let mut i = 0;
    while i < x.len()
        invariant
            0 <= i <= x.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] as int == -(x[j] as int + 1),
        decreases x.len() - i
    {
        let val = x[i];
        // Compute bitwise NOT as -(val + 1)
        // First convert to int to avoid overflow
        let val_int: int = val as int;
        let not_val_int: int = -(val_int + 1);
        
        // Assert that the result is in i8 range
        assert(-128 <= val_int <= 127);  // val is i8
        assert(-128 <= val_int + 1 <= 128);  // adding 1
        assert(-128 <= not_val_int <= 128);  // negating
        assert(-128 <= not_val_int <= 127);  // actually in i8 range
        
        // Convert back to i8
        let not_val: i8 = not_val_int as i8;
        
        assert(not_val as int == -(val as int + 1));
        result.push(not_val);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}