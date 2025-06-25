// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn Main(xInit: int, y: int) -> (z: int)
    requires xInit >= 0,
             y >= 0
    ensures z == 0
{
}

}