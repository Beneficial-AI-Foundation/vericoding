// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn sumElems(v: Vec<int>) -> (sum: int)
//ensures sum==SumL(v[0..v.Length])
    ensures sum==SumL(v[0..v.len()]),
            sum==SumR(v[..])
//,
            sum==SumV(v,0,v.len())
{
}

}