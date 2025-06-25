// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn MinLengthSublist(s: Seq<Seq<int>>) -> (minSublist: Seq<int>)
    requires s.len() > 0
    ensures minSublist in s,
            forall|sublist: int| sublist in s ==> minSublist.len() <= sublist.len()
{
}

}