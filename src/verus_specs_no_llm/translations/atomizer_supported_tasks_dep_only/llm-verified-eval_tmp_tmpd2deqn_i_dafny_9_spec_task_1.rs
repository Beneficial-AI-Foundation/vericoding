// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn max(numbers: Seq<int>) -> (result: int)
    requires numbers != []
    ensures isMax(result, numbers)
{
}

}