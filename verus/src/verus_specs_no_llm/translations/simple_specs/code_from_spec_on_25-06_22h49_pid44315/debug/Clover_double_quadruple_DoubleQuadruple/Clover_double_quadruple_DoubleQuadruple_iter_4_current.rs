use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn DoubleQuadruple(x: i32) -> (a: i32, b: i32)
    ensures
        a == 2 * x && b == 4 * x
{
    let result_a = 2 * x;
    let result_b = 4 * x;
    
    (result_a, result_b)
}

}