use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Max(x: nat, y: nat) -> (r: nat)
    ensures r >= x && r >= y
    ensures r == x || r == y
{
    if x >= y {
        x
    } else {
        y
    }
}

// Test method that demonstrates Max works correctly
fn Test() -> (r: nat)
    ensures r >= 5 && r >= 3
    ensures r == 5 || r == 3
{
    let result = Max(5, 3);
    // Add proof block to help verification
    proof {
        // The postcondition of Max guarantees:
        // result >= 5 && result >= 3
        // result == 5 || result == 3
        // Since 5 >= 3, Max(5, 3) returns 5
        assert(result == 5);
        assert(result >= 5 && result >= 3);
    }
    result
}

}