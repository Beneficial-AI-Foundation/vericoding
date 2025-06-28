use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn CountLists(lists: Seq<Seq<int>>) -> (count: nat)
    ensures
        count >= 0,
        count == lists.len()
{
    let count = lists.len();
    count
}

}