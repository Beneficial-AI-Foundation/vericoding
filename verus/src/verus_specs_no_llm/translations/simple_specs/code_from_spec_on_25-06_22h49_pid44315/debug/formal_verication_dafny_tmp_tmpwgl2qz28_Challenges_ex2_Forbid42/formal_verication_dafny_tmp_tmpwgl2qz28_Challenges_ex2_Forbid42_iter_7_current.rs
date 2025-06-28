use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Forbid42(x: int, y: int) -> (z: int)
    requires
        y != 42
    ensures
        z == x/(42-y)
{
    let divisor = 42 - y;
    assert(divisor != 0) by {
        assert(y != 42);
        if divisor == 0 {
            assert(42 - y == 0);
            assert(42 == y);
            assert(y == 42);
            assert(false);
        }
    };
    x / divisor
}

}