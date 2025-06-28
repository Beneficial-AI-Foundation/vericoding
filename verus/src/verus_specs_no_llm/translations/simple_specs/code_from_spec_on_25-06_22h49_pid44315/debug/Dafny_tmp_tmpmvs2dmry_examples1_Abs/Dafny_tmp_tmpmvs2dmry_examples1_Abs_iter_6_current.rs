use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_abs(x: int) -> int {
    if x >= 0 { x } else { -x }
}

fn Abs(x: int) -> (y: int)
    requires
        x > int::MIN  // Ensure -x doesn't overflow
    ensures
        y >= 0,
        x >= 0 ==> x == y,
        x < 0 ==> -x == y,
        y == spec_abs(x)
{
    if x >= 0 {
        x
    } else {
        -x
    }
}

}