use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
    // Empty main function is valid
}

spec fn square(a: int) -> int {
    a * a
}

// Adding a simple proof function to demonstrate the square spec function works
proof fn test_square_properties() {
    assert(square(0) == 0);
    assert(square(1) == 1);
    assert(square(2) == 4);
    assert(square(-1) == 1);
}

}