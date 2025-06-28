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
        n
    } else {
        let d_u32 = d as u32;
        let shift_right_amount = (32 - d) as u32;
        
        let left_part = n << d_u32;
        let right_part = n >> shift_right_amount;
        let result = left_part | right_part;
        
        result
    }
}

}