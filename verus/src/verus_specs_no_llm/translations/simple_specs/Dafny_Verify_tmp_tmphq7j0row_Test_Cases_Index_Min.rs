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

fn Min(x: int, y: int) -> (m: int)
    ensures
        m <= x && m <= y,
        m == x || m == y
{
    return 0;
}

}