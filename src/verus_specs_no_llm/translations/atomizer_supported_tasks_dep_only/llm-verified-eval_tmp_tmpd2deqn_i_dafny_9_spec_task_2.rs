// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn rolling_max(numbers: Seq<int>) -> (result: Seq<int>)
    requires numbers != []
    ensures result.len() == numbers.len(),
            forall|i: int| 0 < i < result.len() ==> isMax(result[i], numbers[0..(i+1)])
{
}

}