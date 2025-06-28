use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn nonZeroReturn(x: int) -> (y: int)
    ensures y != 0
{
    // We need to ensure we always return a non-zero value
    // If x + 1 would be zero (i.e., x == -1), return 1 instead
    // Otherwise return x + 1
    if x == -1 {
        1
    } else {
        x + 1
    }
}

fn test() -> (y: int)
    ensures y != 0
{
    // Return any non-zero value to satisfy the postcondition
    1
}

}