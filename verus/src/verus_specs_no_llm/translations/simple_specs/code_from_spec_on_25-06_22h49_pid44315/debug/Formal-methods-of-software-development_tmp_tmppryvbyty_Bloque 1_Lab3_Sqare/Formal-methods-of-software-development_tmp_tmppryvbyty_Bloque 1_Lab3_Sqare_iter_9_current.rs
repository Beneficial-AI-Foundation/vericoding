use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
    // Empty main function is valid
}

spec fn Square(a: int) -> int {
    a * a
}

// Adding a simple proof function to demonstrate the Square spec function works
proof fn test_square_properties() {
    assert(Square(0) == 0);
    assert(Square(1) == 1);
    assert(Square(2) == 4);
    assert(Square(-1) == 1);
}

}