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

fn plus_one(x: int) -> (r: int)
    requires
        x >= 0;
    ensures
        r == x + 1;
{
    return 0;
}

}