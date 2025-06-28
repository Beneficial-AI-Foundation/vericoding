use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn SwapArithmetic(X: int, Y: int) -> (x: int, y: int)
    ensures
        x == Y,
        y == X,
{
    let result = (Y, X);
    proof {
        // The postcondition follows directly from the return value
        assert(result.0 == Y);
        assert(result.1 == X);
    }
    result
}

}