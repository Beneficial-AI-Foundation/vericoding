use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn SwapBitvectors(X: u8, Y: u8) -> (x: u8, y: u8)
    ensures
        x == Y,
        y == X
{
    (Y, X)
}

}