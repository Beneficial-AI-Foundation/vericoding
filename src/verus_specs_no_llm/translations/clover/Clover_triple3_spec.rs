// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn Triple(x: int) -> (r: int)
    ensures r==3*x
{
}

}