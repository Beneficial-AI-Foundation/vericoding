use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn peasantMult(a: int, b: int) -> (r: int)
    requires
        b > 0
    ensures
        r == a * b
    decreases b
{
    if b == 1 {
        a
    } else if b % 2 == 0 {
        peasantMult(2 * a, b / 2)
    } else {
        a + peasantMult(2 * a, (b - 1) / 2)
    }
}

}