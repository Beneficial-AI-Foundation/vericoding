use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn simple(y: int) -> (result: int)
    requires
        y == 6
    ensures
        result == 7
{
    let x = y + 1;
    assert(y == 6); // This follows from the precondition
    assert(x == y + 1); // Definition of x
    assert(x == 6 + 1) by {
        assert(y == 6); // Use the precondition
        assert(x == y + 1); // Definition of x
    };
    assert(x == 7); // Arithmetic
    x
}

}