use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn HasOppositeSign(a: int, b: int) -> (result: bool)
    ensures
        result <==> (a < 0 && b > 0) || (a > 0 && b < 0)
{
    let opposite_signs = (a < 0 && b > 0) || (a > 0 && b < 0);
    opposite_signs
}

}