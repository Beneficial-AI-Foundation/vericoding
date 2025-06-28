use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Max(a: int, b: int) -> (c: int)
    ensures
        c >= a,
        c >= b
{
    if a >= b {
        return a;
    } else {
        return b;
    }
}

}