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
    
    // Help Verus connect the ensures clauses
    // From MaxSum postcondition: s == x + y where y = x
    assert(s == x + x) by {
        // s == x + x follows directly from MaxSum's ensures s == x + y with y = x
    };
    
    // From MaxSum postcondition: m == if x >= y { x } else { y } where y = x
    assert(m == x) by {
        // Since x >= x is always true, m == x
        assert(x >= x);
    };
    
    (x, s, m)
}

}