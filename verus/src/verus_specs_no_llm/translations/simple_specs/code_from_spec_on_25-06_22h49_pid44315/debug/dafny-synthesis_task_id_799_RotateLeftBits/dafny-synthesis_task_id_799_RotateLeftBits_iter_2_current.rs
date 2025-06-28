use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn RotateLeftBits(n: u32, d: int) -> (result: u32)
    requires
        0 <= d < 32
    ensures
        result == ((n << d) | (n >> (32 - d)))
{
    let d_u32 = d as u32;
    
    // Prove that d_u32 < 32 for left shift safety
    assert(d_u32 < 32);
    
    // Prove that (32 - d_u32) is valid and < 32 for right shift safety
    assert(d_u32 < 32);
    assert(32 - d_u32 > 0);
    assert(32 - d_u32 <= 32);
    
    let left_part = n << d_u32;
    let right_part = n >> (32 - d_u32);
    
    left_part | right_part
}

}