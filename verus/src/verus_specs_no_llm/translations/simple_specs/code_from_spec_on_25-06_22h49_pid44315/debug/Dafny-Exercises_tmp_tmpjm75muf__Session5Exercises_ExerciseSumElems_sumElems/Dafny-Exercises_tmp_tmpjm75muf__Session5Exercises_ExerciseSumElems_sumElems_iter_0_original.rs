// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn sumElems(v: Vec<int>) -> (sum: int)
//ensures sum==SumL(v[0..v.Length])
    ensures
        sum==SumL(v.spec_index(0..v.len())),
        sum==SumR(v.spec_index(..))
//,
        sum==SumV(v,0,v.len())
{
    return 0;
}

}