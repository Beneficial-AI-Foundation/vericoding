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
    // The assertions are redundant since they follow from the postcondition of Max
    // but we can keep them for clarity
    assert(result >= 5 && result >= 3);
    assert(result == 5 || result == 3);
    result
}

}