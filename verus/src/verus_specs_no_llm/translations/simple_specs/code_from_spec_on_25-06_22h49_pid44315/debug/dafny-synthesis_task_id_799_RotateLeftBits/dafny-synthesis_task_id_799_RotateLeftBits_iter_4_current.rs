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
    if d == 0 {
        // When d = 0, no rotation needed
        // Left shift by 0: n << 0 = n
        // Right shift by 32: n >> 32 = 0 (conceptually)
        // So result should be n | 0 = n
        assert((n << 0u32) == n);
        assert(((32 - 0) as u32) == 32u32);
        // The postcondition expects n >> 32, which equals 0 for the rotation
        n
    } else {
        let d_u32 = d as u32;
        let shift_right_amount = (32 - d) as u32;
        
        // Prove shift amounts are valid
        assert(0 < d < 32);
        assert(d_u32 < 32);
        assert(0 < 32 - d < 32);
        assert(shift_right_amount < 32);
        
        let left_part = n << d_u32;
        let right_part = n >> shift_right_amount;
        let result = left_part | right_part;
        
        result
    }
}

}