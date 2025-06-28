// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn CountLists(lists: Seq<Seq<int>>) -> (count: int)
    ensures
        count >= 0,
        count == lists.len()
{
    return 0;
}

}