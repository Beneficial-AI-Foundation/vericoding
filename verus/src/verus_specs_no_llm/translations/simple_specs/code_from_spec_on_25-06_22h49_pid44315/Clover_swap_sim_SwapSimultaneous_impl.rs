use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn SwapSimultaneous(X: int, Y: int) -> (x: int, y: int)
    ensures
        x == Y,
        y == X,
{
    let result = (Y, X);
    assert(result.0 == Y);
    assert(result.1 == X);
    result
}

}