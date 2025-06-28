use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn problem2(p: int, q: int, X: int, Y: int) -> (r: int, s: int)
    requires
        p == 2*X + Y && q == X + 3
    ensures
        r == X && s == Y
{
    let x = q - 3;
    let y = p - 2*q + 6;
    
    // Verify our solution satisfies the original equations
    assert(q == x + 3);  // By construction: q == (q - 3) + 3
    assert(p == 2*x + y); // By construction: p == 2*(q - 3) + (p - 2*q + 6) == p
    
    return (x, y);
}

}

The solution works by: