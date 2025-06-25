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

fn problem3(m: int, X: int) -> (r: int)
    requires
        X >= 0 && (2*m == 1 - X || m == X + 3)
    ensures
        r == X
{
    return 0;
}

}