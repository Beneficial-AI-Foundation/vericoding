// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn main() {
}

fn euclidianDiv(a: int, b: int) -> (q: int, r: int)
    requires
        a >= 0,
        b > 0
    ensures
        a == b * q + r
{
    return (0, 0);
}

}