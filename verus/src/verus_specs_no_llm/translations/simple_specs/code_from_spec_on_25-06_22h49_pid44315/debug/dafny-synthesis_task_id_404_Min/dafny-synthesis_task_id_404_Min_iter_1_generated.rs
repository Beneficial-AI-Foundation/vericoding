use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Min(a: int, b: int) -> (minValue: int)
    ensures
        minValue == a || minValue == b,
        minValue <= a && minValue <= b
{
    if a <= b {
        a
    } else {
        b
    }
}

}