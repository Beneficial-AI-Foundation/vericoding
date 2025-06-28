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
        a >= b && Par(a - b)
{
    let diff = a - b;
    
    // Add proof block to help verification understand the preconditions
    proof {
        assert(diff >= 0);
        assert(diff % 2 == 0);
    }
    
    (diff / 2, a + b)
}

}