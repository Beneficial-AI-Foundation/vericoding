// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn MaxLengthList(lists: Seq<Seq<int>>) -> (maxList: Seq<int>)
    requires lists.len() > 0
    ensures forall|l: int| l in lists ==> l.len() <= maxList.len(),
            maxList in lists
{
}

}