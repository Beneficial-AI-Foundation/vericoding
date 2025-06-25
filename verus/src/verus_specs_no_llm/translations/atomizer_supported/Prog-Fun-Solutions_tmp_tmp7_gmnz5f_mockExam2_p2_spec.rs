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

fn problem2(p: int, q: int, X: int, Y: int) -> (r: int, s: int)
    requires
        p == 2*X + Y && q == X + 3
    ensures
        r == X && s == Y
{
    return (0, 0);
}

}