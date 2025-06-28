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
    (n << d_u32) | (n >> (32 - d_u32))
}

}