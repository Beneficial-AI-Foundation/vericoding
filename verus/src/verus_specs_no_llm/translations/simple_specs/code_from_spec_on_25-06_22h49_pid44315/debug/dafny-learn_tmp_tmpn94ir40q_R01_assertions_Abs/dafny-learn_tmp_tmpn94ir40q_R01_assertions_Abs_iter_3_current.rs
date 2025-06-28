use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Abs(x: int) -> (y: int)
    ensures
        0 <= y,
        x < 0 ==> y == -x,
        x >= 0 ==> y == x
{
    if x < 0 {
        -x
    } else {
        x
    }
}

}