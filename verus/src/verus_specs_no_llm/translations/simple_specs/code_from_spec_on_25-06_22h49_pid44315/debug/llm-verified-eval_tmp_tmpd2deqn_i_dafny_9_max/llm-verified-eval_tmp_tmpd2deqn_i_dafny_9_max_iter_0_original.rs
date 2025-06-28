// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn max(numbers: Seq<int>) -> (result: int)
    requires
        numbers != []
    ensures
        isMax(result, numbers)
{
    return 0;
}

}