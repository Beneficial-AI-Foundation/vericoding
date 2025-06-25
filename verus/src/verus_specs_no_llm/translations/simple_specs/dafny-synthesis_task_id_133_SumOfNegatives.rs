// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn main() {
}

fn SumOfNegatives(a: Vec<int>) -> (result: int)
    ensures
        result == sumNegativesTo(a, a.len())
{
    return 0;
}

}