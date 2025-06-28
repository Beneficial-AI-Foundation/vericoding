// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Max(x: int, y: int) -> (m: int)
{
    if x >= y {
        x
    } else {
        y
    }
}

}