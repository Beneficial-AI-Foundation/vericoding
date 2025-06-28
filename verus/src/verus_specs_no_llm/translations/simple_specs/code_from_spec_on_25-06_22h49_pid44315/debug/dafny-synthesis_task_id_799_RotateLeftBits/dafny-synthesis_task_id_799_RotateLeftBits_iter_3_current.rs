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
    
    // Prove that d_u32 < 32 for left shift safety
    assert(d < 32);
    assert(d_u32 < 32);
    
    // Prove that (32 - d) is valid and positive for right shift safety
    assert(d >= 0);
    assert(32 - d > 0);
    assert(32 - d <= 32);
    
    let shift_right_amount = (32 - d) as u32;
    assert(shift_right_amount > 0);
    assert(shift_right_amount <= 32);
    
    let left_part = n << d_u32;
    let right_part = n >> shift_right_amount;
    
    let result = left_part | right_part;
    
    // Help Verus understand the equivalence
    assert(d_u32 == (d as u32));
    assert(shift_right_amount == ((32 - d) as u32));
    
    result
}

}