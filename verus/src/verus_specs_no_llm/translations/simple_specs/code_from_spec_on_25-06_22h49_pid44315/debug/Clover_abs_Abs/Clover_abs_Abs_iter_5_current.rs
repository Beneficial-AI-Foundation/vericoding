use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Abs(x: int) -> (y: int)
    ensures
        x >= 0 ==> x == y,
        x < 0 ==> x + y == 0
{
    if x >= 0 {
        x
    } else {
        let result = -x;
        assert(x + result == 0) by {
            assert(x + (-x) == 0);
        }
        result
    }
}

}