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
        // When x != -1, we have x + 1 != 0
        // This is because x + 1 == 0 implies x == -1, which contradicts our condition
        assert(x != -1);
        assert(x + 1 != 0) by {
            // Proof by contradiction: if x + 1 == 0, then x == -1
            // But we know x != -1, so x + 1 != 0
            if x + 1 == 0 {
                assert(x == -1); // This contradicts x != -1
            }
        };
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