use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn RotateLeftBits(n: u32, d: int) -> (result: u32)
    requires
        0 <= d < 32
    ensures
        result == ((n << (d as u32)) | (n >> ((32 - d) as u32)))
{
    let d_u32 = d as u32;
    let shift_right_amount = (32 - d) as u32;
    
    // Proof assertions to help Verus verify the preconditions for bit operations
    assert(0 <= d < 32);
    assert(d_u32 < 32);
    assert(shift_right_amount <= 32);
    assert(shift_right_amount > 0 || d == 0);
    
    let left_part = n << d_u32;
    let right_part = n >> shift_right_amount;
    let result = left_part | right_part;
    
    // Help Verus understand that our computation matches the postcondition
    assert(left_part == n << (d as u32));
    assert(right_part == n >> ((32 - d) as u32));
    assert(result == (n << (d as u32)) | (n >> ((32 - d) as u32)));
    
    result
}

}