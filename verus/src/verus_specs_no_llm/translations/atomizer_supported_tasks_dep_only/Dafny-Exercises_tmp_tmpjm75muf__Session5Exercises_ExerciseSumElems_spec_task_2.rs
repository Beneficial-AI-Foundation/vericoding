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

fn sumElemsB(v: Vec<int>) -> (sum: int)
//ensures sum==SumL(v[0..v.Length])
    ensures
        sum==SumL(v.spec_index(0..v.len())),
        sum==SumR(v.spec_index(0..v.len()))
{
    return 0;
}

}