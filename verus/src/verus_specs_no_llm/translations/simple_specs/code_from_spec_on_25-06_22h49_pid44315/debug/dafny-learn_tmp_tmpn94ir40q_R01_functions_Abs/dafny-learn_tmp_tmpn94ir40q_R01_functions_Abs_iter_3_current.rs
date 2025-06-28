use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Abs(x: int) -> (y: int)
    ensures
        y >= 0,
        y == if x >= 0 { x } else { -x }
{
    if x >= 0 {
        x
    } else {
        -x
    }
}

}