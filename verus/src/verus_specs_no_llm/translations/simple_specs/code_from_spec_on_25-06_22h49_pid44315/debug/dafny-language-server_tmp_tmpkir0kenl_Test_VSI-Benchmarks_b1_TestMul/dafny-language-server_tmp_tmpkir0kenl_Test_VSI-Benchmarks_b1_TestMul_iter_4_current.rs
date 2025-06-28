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

fn TestMul(x: int, y: int) -> (r: (int, int))
    ensures 
        r.0 == x * y,
        r.1 == x + y
{
    let mul_val = Mul(x, y);
    let add_val = Add(x, y);
    (mul_val, add_val)
}

}