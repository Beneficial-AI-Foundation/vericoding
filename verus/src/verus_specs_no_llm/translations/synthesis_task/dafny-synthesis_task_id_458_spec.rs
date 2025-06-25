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

fn RectangleArea(length: int, width: int) -> (area: int)
    requires
        length > 0,
        width > 0
    ensures
        area == length * width
{
    return 0;
}

}