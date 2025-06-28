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
        proof {
            // Proof by contradiction: assume x + 1 == 0
            // Then x == -1, but we know x != -1
            // Therefore x + 1 != 0
            assert(x != -1);
            if x + 1 == 0 {
                assert(x == -1); // This would contradict x != -1
                assert(false);   // Contradiction
            }
        }
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