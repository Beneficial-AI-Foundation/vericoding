// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn max(x: int, y: int) -> (m: int)
    requires
        true
    ensures
        m >= x && m >= y && (m == x || m == y)
{
    if x >= y {
        x
    } else {
        y
    }
}

}