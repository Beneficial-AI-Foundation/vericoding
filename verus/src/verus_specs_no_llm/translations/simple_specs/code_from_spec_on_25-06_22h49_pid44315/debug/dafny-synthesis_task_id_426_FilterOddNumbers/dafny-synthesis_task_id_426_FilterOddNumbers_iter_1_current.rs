use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
    // Main function can be empty or contain some basic operations
    // Since no specific requirements are given, leaving it empty is fine
}

spec fn IsOdd(n: int) -> bool {
    n % 2 != 0
}

// Adding some test functions to demonstrate the spec function works
proof fn test_is_odd_examples() {
    assert(IsOdd(1));
    assert(IsOdd(3));
    assert(IsOdd(-1));
    assert(!IsOdd(0));
    assert(!IsOdd(2));
    assert(!IsOdd(4));
    assert(!IsOdd(-2));
}

}