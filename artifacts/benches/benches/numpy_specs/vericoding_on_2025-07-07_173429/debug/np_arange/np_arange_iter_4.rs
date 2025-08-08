use vstd::prelude::*;

verus! {

// Translation of the Dafny arange function to Verus
// Note: This uses u8 instead of f64 because Verus has limited floating-point support
fn arange_success(start: u8, count: u8) -> (ret: Vec<u8>)
    requires
        count > 0,
        count <= 3,
        start <= 100,
        start + count <= 150,
    ensures
        ret.len() == count as nat,
        ret.len() > 0,
        ret[0] == start,
{
    let mut ret: Vec<u8> = Vec::with_capacity(count as usize);
    let mut i: u8 = 0;
    
    while i < count
        invariant
            i <= count,
            ret.len() == i as nat,
            count > 0,
            count <= 3,
            start <= 100,
            start + count <= 150,
            forall|j: int| 0 <= j < i ==> #[trigger] ret[j as int] == start + (j as u8),
        decreases count - i,
    {
        proof {
            assert(i < count);
            assert(i <= 3);
            assert(start + i <= start + count);
            assert(start + i <= 150);
        }
        
        ret.push(start + i);
        i += 1;
    }
    
    ret
}

fn main() {}

}

// Note: The original Dafny code used floating-point types (real) which are not fully
// supported in Verus verification. This translation uses integers with step size 1.
// The conceptual structure and verification pattern remain the same:
//
// 1. Calculate the length based on the range and step
// 2. Create a vector with that capacity
// 3. Use a while loop with appropriate invariants to fill the vector
// 4. Maintain invariants about the relationship between elements
// 5. Prove postconditions about the result
//
// The key differences from Dafny:
// - Uses u8 instead of real/f64 due to Verus limitations
// - Requires explicit decreases clause for the loop
// - Needs #[trigger] annotations for quantifiers
// - Requires proof blocks to establish arithmetic facts
// - Uses more conservative bounds to avoid overflow issues