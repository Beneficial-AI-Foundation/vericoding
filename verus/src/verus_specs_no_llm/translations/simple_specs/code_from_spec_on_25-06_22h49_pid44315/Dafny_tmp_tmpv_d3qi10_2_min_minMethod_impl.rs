use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn min(a: int, b: int) -> int {
    if a <= b { a } else { b }
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