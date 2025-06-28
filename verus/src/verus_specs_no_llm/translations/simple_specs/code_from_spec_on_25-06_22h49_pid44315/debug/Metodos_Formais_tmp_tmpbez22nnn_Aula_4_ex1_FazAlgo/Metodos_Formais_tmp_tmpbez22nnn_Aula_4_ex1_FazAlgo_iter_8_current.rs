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
    let x = diff / 2;
    let y = a + b;
    
    // Proof block to establish the postconditions
    proof {
        // Establish that diff is non-negative
        assert(diff >= 0);
        
        // Establish that diff is even
        assert(Par(diff));
        assert(diff % 2 == 0);
        
        // For even numbers, division is exact
        assert(x == diff / 2);
        assert(y == a + b);
    }
    
    (x, y)
}

}