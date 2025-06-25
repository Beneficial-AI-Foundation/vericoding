// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn Sqare2(a: int) -> (x: int)
    requires a>=1
    ensures x == a*a
{
}

}