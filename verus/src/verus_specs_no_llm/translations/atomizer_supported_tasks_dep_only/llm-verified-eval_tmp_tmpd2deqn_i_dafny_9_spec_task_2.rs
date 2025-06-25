// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn rolling_max(numbers: Seq<int>) -> (result: Seq<int>)
    requires
        numbers != []
    ensures
        result.len() == numbers.len(),
        forall i :: 0 < i < result.len() ==> isMax(result.spec_index(i), numbers.spec_index(0..(i+1)))
{
    return Seq::empty();
}

}