use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_abs(x: int) -> int {
    if x >= 0 { x } else { -x }
}

fn Abs(x: i64) -> (y: i64)
    requires
        x > i64::MIN  // Ensure -x doesn't overflow
    ensures
        y >= 0,
        x >= 0 ==> x == y,
        x < 0 ==> -x == y,
        y == spec_abs(x as int)
{
    if x >= 0 {
        x
    } else {
        -x
    }
}

}