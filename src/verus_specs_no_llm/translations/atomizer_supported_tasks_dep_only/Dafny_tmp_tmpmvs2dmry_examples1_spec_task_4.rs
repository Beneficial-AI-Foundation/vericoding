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

fn Max(x: int, y: int) -> (a: int)
    ensures
        a == x || a == y;,
        x > y ==> a == x;,
        x <= y ==> a == y;
{
    return 0;
}

}