use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_abs(x: int) -> int {
    if x >= 0 { x } else { -x }
}

fn Abs(x: int) -> (y: int)
    ensures
        y >= 0,
        x >= 0 ==> x == y,
        x < 0 ==> -x == y,
        y == spec_abs(x)
{
    if x >= 0 {
        assert(x >= 0);
        assert(spec_abs(x) == x);
        x
    } else {
        assert(x < 0);
        let neg_x = -x;
        assert(neg_x >= 0);
        assert(spec_abs(x) == neg_x);
        neg_x
    }
}

}