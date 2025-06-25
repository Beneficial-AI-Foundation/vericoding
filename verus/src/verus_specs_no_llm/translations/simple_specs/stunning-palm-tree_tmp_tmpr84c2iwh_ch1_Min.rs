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

fn Min(x: int, y: int) -> (r: int)
    ensures
        r <= x && r <= y,
        r == x || r == y
{
    return 0;
}

}