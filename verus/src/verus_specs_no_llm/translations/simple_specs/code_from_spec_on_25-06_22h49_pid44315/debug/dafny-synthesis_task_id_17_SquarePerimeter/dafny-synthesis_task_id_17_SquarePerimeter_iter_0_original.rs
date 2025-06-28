// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn SquarePerimeter(side: int) -> (perimeter: int)
    requires
        side > 0
    ensures
        perimeter == 4 * side
{
    return 0;
}

}