use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn Par(n: int) -> bool {
    n % 2 == 0
}

fn FazAlgo(a: int, b: int) -> (x: int, y: int)
    requires
        a >= b,
        Par(a - b),
    ensures
        result.0 == (a - b) / 2 && result.1 == a + b
{
    let diff = a - b;
    
    // Add proof block to help verification understand the division
    proof {
        assert(diff >= 0);
        assert(Par(diff));
        assert(diff % 2 == 0);
        // Help Verus understand that division by 2 is well-defined for even numbers
        assert(diff == 2 * (diff / 2));
    }
    
    (diff / 2, a + b)
}

}

The key changes made:


   - `diff >= 0` (from `a >= b`)
   - `Par(diff)` (from the precondition)
   - `diff % 2 == 0` (from the definition of `Par`)
   - The division relationship for even numbers

This helps Verus verify that `(diff / 2)` in the return statement indeed equals `(a - b) / 2` as required by the postcondition.