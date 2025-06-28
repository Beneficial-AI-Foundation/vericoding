use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn bar(x: int, y: int) -> (r: int)
    requires
        y >= 0
    ensures
        r == x + y
{
    x + y
}

// Adding a proof function to demonstrate the spec function works correctly
proof fn test_bar()
    ensures
        bar(5, 3) == 8,
        bar(0, 0) == 0,
        bar(-10, 15) == 5
{
    // Add explicit assertions to help Verus verify the ensures clauses
    assert(bar(5, 3) == 8);
    assert(bar(0, 0) == 0);
    assert(bar(-10, 15) == 5);
}

}