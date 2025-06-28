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
    let result = y + 1;
    assert(y == 6); // This follows from the precondition
    assert(result == 6 + 1); // Basic arithmetic
    assert(result == 7); // Therefore result == 7
    result
}

}