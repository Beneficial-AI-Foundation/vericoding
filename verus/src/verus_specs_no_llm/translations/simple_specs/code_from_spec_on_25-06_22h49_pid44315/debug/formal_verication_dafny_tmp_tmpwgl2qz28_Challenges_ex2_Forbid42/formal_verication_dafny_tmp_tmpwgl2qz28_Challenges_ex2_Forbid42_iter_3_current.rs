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
    assert(divisor != 0);
    x / divisor
}

}