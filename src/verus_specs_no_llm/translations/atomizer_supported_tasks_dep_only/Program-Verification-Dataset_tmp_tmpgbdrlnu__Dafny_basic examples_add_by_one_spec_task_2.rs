// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn bar(x: int, y: int) -> (r: int)
    requires y >= 0;
    ensures r == x + y;
{
}

}