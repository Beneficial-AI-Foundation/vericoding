// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn CountToAndReturnN(n: int) -> (r: int)
    requires n >= 0
    ensures r == n
{
}

}