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

fn Min(x: int, y: int) -> (z: int)
    ensures
        x<=y ==> z==x,
        x>y ==> z==y
{
    return 0;
}

}