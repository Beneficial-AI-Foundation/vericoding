// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn mCountMin(v: Vec<int>) -> (c: int)
    requires v.len()>0
    ensures c==countMin(v,min(v,v.len()),v.len())
//Implement and verify an O(v.len()) algorithm
{
}

}