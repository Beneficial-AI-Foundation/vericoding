// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn PairwiseAddition(a: Vec<int>) -> (result: Vec<int>)
    requires a != null,
             a.len() % 2 == 0
    ensures result != null,
            result.len() == a.len() / 2,
            forall|i: int| 0 <= i < result.len() ==> result[i] == a[2*i] + a[2*i + 1]
{
}

}