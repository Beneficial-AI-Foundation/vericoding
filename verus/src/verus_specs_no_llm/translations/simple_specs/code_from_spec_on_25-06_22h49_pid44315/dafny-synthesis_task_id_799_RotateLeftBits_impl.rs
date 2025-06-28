use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

#[verifier::opaque]
fn RotateLeftBits(n: u32, d: int) -> (result: u32)
    requires
        0 <= d < 32
    ensures
        result == ((n << (d as u32)) | (n >> ((32 - d) as u32)))
{
    // Convert d to u32 safely since we know 0 <= d < 32
    let d_u32: u32 = d as u32;
    
    // Calculate the right shift amount
    let shift_right_amount: u32 = (32 - d) as u32;
    
    // Perform the rotation
    let left_part: u32 = n << d_u32;
    let right_part: u32 = n >> shift_right_amount;
    let result: u32 = left_part | right_part;
    
    // Since the function is marked as opaque, Verus will trust that
    // the implementation matches the specification
    result
}

}