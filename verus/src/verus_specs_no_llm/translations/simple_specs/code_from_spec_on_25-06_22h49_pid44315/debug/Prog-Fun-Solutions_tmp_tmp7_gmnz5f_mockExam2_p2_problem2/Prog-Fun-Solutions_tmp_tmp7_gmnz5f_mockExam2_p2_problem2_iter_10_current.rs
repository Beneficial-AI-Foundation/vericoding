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
    
    // Prove that x == X
    assert(x == q - 3);
    assert(q == X + 3);
    assert(x == (X + 3) - 3) by {
        assert(x == q - 3);
        assert(q == X + 3);
    };
    assert(x == X) by {
        assert(x == (X + 3) - 3);
        // Verus can handle this arithmetic automatically
    };
    
    // Prove that y == Y
    assert(y == p - 2*q + 6);
    assert(p == 2*X + Y);
    assert(q == X + 3);
    assert(y == (2*X + Y) - 2*(X + 3) + 6) by {
        assert(y == p - 2*q + 6);
        assert(p == 2*X + Y);
        assert(q == X + 3);
    };
    assert(y == 2*X + Y - 2*X - 6 + 6) by {
        assert(y == (2*X + Y) - 2*(X + 3) + 6);
        // Expand 2*(X + 3) = 2*X + 6
    };
    assert(y == Y) by {
        assert(y == 2*X + Y - 2*X - 6 + 6);
        // Simplify: 2*X - 2*X = 0, -6 + 6 = 0
    };
    
    (x, y)
}

}