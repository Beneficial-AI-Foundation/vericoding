use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Abs(x: int) -> (y: int)
    ensures
        y >= 0,
        x >= 0 ==> x == y,
        x < 0 ==> -x == y,
        y == abs(x)
{
    if x >= 0 {
        assert(x >= 0);
        assert(abs(x) == x);
        x
    } else {
        assert(x < 0);
        assert(-x >= 0);
        assert(abs(x) == -x);
        -x
    }
}

}