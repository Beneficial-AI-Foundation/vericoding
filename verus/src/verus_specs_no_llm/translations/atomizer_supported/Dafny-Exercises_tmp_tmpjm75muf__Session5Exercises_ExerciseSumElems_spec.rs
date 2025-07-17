// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn SumR(s: Seq<int>) -> int
{
    0
}

spec fn spec_sumElems(v: Vec<int>) -> sum:int)
//ensures sum==SumL(v[0..v.Length]
    ensures
        sum==SumL(v.index(0..v.len())),
        sum==SumR(v.index(..))
//,
        sum==SumV(v,0,v.len())
;

proof fn lemma_sumElems(v: Vec<int>) -> (sum: int)
//ensures sum==SumL(v[0..v.Length])
    ensures
        sum==SumL(v.index(0..v.len())),
        sum==SumR(v.index(..))
//,
        sum==SumV(v,0,v.len())
{
    0
}

}