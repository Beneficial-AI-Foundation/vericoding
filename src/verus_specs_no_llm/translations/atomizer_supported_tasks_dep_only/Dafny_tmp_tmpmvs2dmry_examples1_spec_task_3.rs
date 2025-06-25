// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn MultiReturn(x: int, y: int) -> more: int, less: int
    requires y>=0;
    ensures less <= x <= more;
{
}

}