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
        -x
    }
}

}