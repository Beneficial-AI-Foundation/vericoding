use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn minMethod(a: int, b: int) -> (c: int)
    ensures
        c <= a && c <= b,
        c == a || c == b,
        c == min(a, b)
{
    if a <= b {
        a
    } else {
        b
    }
}

}