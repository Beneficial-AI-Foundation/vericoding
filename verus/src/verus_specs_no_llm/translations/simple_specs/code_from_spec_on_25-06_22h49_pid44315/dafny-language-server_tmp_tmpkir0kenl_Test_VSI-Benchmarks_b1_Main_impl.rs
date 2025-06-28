use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Mul(x: int, y: int) -> (r: int)
    ensures r == x * y
{
    x * y
}

fn TestMul(x: int, y: int) -> (r: int)
    ensures r == x * y
{
    Mul(x, y)
}

}