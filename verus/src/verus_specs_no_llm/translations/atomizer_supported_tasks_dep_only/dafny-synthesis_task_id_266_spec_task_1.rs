// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn LateralSurfaceArea(size: int) -> (area: int)
    requires
        size > 0
    ensures
        area == 4 * size * size
{
    return 0;
}

}