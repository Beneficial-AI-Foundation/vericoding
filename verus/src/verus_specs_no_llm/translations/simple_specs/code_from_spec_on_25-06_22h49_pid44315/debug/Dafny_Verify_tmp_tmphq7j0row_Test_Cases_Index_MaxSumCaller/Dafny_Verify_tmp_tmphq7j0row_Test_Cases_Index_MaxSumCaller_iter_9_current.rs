use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn MaxSum(x: int, y: int) -> (s: int, m: int)
    ensures s == x + y,
    ensures m == if x >= y { x } else { y },
{
    let s = x + y;
    let m = if x >= y { x } else { y };
    (s, m)
}

fn MaxSumCaller() -> (x: int, s: int, m: int)
    ensures s == x + x,
    ensures m == x,
{
    let x = 5;
    let (s, m) = MaxSum(x, x);
    
    // Add proof block to help Verus verify the postconditions
    proof {
        // From MaxSum postcondition: s == x + y where y = x
        assert(s == x + x);
        
        // From MaxSum postcondition: m == if x >= y { x } else { y } where y = x
        // Since x >= x is always true, m == x
        assert(x >= x);
        assert(m == x);
    }
    
    (x, s, m)
}

}