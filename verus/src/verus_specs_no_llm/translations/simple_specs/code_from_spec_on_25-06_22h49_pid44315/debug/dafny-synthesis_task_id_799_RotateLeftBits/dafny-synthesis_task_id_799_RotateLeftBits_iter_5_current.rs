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
        // When d = 0, the specification becomes:
        // result == ((n << 0) | (n >> 32))
        // Since n << 0 == n and n >> 32 == 0 (mathematically), result should be n
        // But we need to match the specification exactly
        let left_part = n << 0u32;
        // For the right shift by 32, we need to handle this as 0
        // Since the spec expects n >> 32, which is 0 for any 32-bit value
        let right_part = 0u32; // This represents n >> 32
        let result = left_part | right_part;
        
        // Prove this matches the specification
        assert(left_part == n);
        assert(right_part == 0);
        assert(result == n);
        
        result
    } else {
        let d_u32 = d as u32;
        let shift_right_amount = (32 - d) as u32;
        
        // Prove shift amounts are valid
        assert(0 < d < 32);
        assert(d_u32 > 0 && d_u32 < 32);
        assert(0 < 32 - d < 32);
        assert(shift_right_amount > 0 && shift_right_amount < 32);
        
        let left_part = n << d_u32;
        let right_part = n >> shift_right_amount;
        let result = left_part | right_part;
        
        result
    }
}

}