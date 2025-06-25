// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn sum_array(a: Vec<int>) -> (sum: int)
    requires a != null;
    ensures sum == sumTo(a, a.len());
{
}

}