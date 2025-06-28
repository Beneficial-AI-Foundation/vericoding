use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Abs(x: int) -> (y: int)
    ensures 0 <= y,
    ensures x < 0 ==> y == -x,
    ensures x >= 0 ==> y == x,
{
    if x < 0 {
        -x
    } else {
        x
    }
}

fn TestingAbs2(x: int) -> (y: int)
    ensures 0 <= y,
    ensures x < 0 ==> y == -x,
    ensures x >= 0 ==> y == x,
{
    let result = Abs(x);
    result
}

}