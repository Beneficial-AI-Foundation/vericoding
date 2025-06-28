use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn nonZeroReturn(x: int) -> (y: int)
    ensures y != 0
{
    // We can return any non-zero value to satisfy the postcondition
    // Using x + 1 ensures we get a non-zero result
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