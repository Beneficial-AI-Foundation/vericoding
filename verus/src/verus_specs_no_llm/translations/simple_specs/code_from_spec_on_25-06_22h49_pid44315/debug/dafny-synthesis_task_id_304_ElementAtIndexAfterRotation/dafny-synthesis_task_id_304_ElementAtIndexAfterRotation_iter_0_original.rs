// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn ElementAtIndexAfterRotation(l: Seq<int>, n: int, index: int) -> (element: int)
    requires
        n >= 0,
        0 <= index < l.len()
    ensures
        element == l.spec_index((index - n + l.len()) % l.len())
{
    return 0;
}

}