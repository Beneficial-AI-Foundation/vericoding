// Translated from Dafny
use builtin::*;
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
    length * width
}

}