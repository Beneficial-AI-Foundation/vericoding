use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn SquarePerimeter(side: u32) -> (perimeter: u32)
    requires
        side > 0,
        side <= u32::MAX / 4,  // Ensure no overflow
    ensures
        perimeter == 4 * side
{
    4 * side
}

}