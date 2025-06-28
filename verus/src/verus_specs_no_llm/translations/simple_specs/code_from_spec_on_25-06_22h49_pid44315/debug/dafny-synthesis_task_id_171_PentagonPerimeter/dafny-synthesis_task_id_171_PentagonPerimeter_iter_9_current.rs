use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn PentagonPerimeter(side: int) -> (perimeter: int)
    requires
        side > 0,
    ensures
        perimeter == 5 * side,
{
    5 * side
}

}