use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn abs(x: int) -> (y: int)
    ensures
        y >= 0,
        y == x || y == -x,
        (x >= 0 ==> y == x),
        (x < 0 ==> y == -x)
{
    if x >= 0 {
        x
    } else {
        -x
    }
}

}