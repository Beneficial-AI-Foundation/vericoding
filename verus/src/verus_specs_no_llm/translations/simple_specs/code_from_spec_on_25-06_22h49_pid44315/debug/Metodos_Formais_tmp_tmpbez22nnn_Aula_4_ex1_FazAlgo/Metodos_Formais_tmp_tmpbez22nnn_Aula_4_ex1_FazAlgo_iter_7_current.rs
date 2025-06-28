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
        assert(diff >= 0) by {
            assert(a >= b);
        };
        assert(Par(diff)) by {
            assert(Par(a - b));
            assert(diff == a - b);
        };
        assert(diff % 2 == 0) by {
            assert(Par(diff));
        };
        // Help Verus understand that division by 2 is well-defined for even numbers
        assert(diff == 2 * (diff / 2)) by {
            assert(diff % 2 == 0);
        };
    }
    
    (diff / 2, a + b)
}

}