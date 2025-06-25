// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn Swap(a: int, b: int) -> (result: Seq<int>)
    ensures result.len() == 2,
            result[0] == b,
            result[1] == a
{
}

}