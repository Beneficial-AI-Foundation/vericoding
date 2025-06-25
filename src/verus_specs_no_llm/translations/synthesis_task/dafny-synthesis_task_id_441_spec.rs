// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn CubeSurfaceArea(size: int) -> (area: int)
    requires size > 0
    ensures area == 6 * size * size
{
}

}