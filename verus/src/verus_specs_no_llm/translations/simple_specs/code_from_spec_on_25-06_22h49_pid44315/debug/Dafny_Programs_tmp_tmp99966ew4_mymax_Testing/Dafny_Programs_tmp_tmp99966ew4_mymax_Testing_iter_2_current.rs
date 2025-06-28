use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Max(a: int, b: int) -> (c: int)
    ensures c >= a && c >= b && (c == a || c == b)
{
    if a >= b {
        a
    } else {
        b
    }
}

fn Testing() -> (result: int)
    ensures result == 10
{
    10
}

}