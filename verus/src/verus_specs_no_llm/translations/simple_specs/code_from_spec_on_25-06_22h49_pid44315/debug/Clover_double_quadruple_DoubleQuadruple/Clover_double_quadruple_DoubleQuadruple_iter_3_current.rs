use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn DoubleQuadruple(x: int) -> (a: int, b: int)
    ensures
        a == 2 * x && b == 4 * x
{
    let result_a = 2 * x;
    let result_b = 4 * x;
    
    // Proof that the postcondition holds
    assert(result_a == 2 * x);
    assert(result_b == 4 * x);
    
    (result_a, result_b)
}

}