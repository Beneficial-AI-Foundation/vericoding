// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn main() {
}

fn CubeSurfaceArea(size: int) -> (area: int)
    requires
        size > 0
    ensures
        area == 6 * size * size
{
    return 0;
}

}