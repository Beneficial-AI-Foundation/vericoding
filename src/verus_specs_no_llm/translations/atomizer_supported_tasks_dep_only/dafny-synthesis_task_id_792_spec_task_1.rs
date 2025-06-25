// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn CountLists(lists: Seq<Seq<int>>) -> (count: int)
    ensures count >= 0,
            count == lists.len()
{
}

}