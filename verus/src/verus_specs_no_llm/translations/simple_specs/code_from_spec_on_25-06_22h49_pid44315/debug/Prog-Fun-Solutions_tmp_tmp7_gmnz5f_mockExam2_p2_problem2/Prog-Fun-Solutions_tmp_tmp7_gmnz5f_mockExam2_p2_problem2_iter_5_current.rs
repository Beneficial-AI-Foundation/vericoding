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
    
    // Prove x == X
    assert(x == q - 3);
    assert(q == X + 3);
    assert(x == (X + 3) - 3);
    assert(x == X);
    
    // Prove y == Y
    assert(y == p - 2*q + 6);
    assert(p == 2*X + Y);
    assert(q == X + 3);
    assert(y == (2*X + Y) - 2*(X + 3) + 6);
    assert(y == 2*X + Y - 2*X - 6 + 6);
    assert(y == Y);
    
    (x, y)
}

}