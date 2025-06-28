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
        let result = x + 1;
        // Add proof assertion to help Verus verify that x + 1 != 0 when x != -1
        assert(x != -1);
        assert(result == x + 1);
        assert(result != 0); // This follows from x != -1, so x + 1 != 0
        result
    }
}

fn test() -> (y: int)
    ensures y != 0
{
    // Return any non-zero value to satisfy the postcondition
    1
}

}