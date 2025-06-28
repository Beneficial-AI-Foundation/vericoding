use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn DoubleQuadruple(x: int) -> (a: int, b: int)
    ensures
        a == 2 * x && b == 4 * x
{
    (2 * x, 4 * x)
}

}