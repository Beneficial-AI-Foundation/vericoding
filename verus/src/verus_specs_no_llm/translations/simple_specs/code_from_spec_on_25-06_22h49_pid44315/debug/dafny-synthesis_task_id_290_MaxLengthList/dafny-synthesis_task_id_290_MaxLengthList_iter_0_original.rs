// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn MaxLengthList(lists: Seq<Seq<int>>) -> (maxList: Seq<int>)
    requires
        lists.len() > 0
    ensures
        forall l :: l in lists ==> l.len() <= maxList.len(),
        maxList in lists
{
    return Seq::empty();
}

}