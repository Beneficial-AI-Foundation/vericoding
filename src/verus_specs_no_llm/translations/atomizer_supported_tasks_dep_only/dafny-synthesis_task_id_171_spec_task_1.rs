// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn PentagonPerimeter(side: int) -> (perimeter: int)
    requires side > 0
    ensures perimeter == 5 * side
{
}

}