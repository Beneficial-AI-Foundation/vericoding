use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn SquarePerimeter(side: nat) -> (perimeter: nat)
    requires
        side > 0
    ensures
        perimeter == 4 * side
{
    4 * side
}

}