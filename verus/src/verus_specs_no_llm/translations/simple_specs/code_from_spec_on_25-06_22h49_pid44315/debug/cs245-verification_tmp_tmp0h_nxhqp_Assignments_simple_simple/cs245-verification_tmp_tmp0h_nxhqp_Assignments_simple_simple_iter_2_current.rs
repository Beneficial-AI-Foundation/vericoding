// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn simple(y: int) -> (x: int)
    requires
        y == 6
    ensures
        x == 7
{
    // Use the precondition to establish the relationship
    // Since we know y == 6 from the precondition, we can return y + 1 = 7
    y + 1
}

}