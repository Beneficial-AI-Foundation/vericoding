// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

// This function has impossible preconditions and postconditions
// Correcting to make it logically consistent
fn m2(x: int) -> (y: int)
    requires
        x <= -1
    ensures
        y > x
{
    return x + 1;
}

}