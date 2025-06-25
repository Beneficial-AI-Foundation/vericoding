// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn vector_Sum(v: Seq<int>) -> (x: int)
    ensures x == sum(v)
{
}

}