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

fn CountTrue(a: Vec<bool>) -> (result: int)
    requires
        a != null
    ensures
        result == countTo(a, a.len())
{
    return 0;
}

}