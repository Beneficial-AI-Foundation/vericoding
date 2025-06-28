use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn PentagonPerimeter(side: int) -> (perimeter: int)
    requires
        side > 0
    ensures
        perimeter == 5 * side
{
    let result = 5 * side;
    assert(result == 5 * side);
    result
}

}