// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn MinLengthSublist(s: Seq<Seq<int>>) -> (minSublist: Seq<int>)
    requires
        s.len() > 0
    ensures
        minSublist in s,
        forall sublist :: sublist in s ==> minSublist.len() <= sublist.len()
{
    return Seq::empty();
}

}