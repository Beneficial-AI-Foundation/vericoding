// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn copyArr(a: Vec<int>, l: int, r: int) -> (ret: Vec<int>)
    requires 0 <= l < r <= a.len()
    ensures ret[..] == a[l..r]
{
}

}