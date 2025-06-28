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

fn Add(x: int, y: int) -> (r: int)
    ensures r == x + y
{
    x + y
}

fn TestMul(x: int, y: int) -> (mul_result: int, add_result: int)
    ensures 
        mul_result == x * y,
        add_result == x + y
{
    let mul_result = Mul(x, y);
    let add_result = Add(x, y);
    (mul_result, add_result)
}

}