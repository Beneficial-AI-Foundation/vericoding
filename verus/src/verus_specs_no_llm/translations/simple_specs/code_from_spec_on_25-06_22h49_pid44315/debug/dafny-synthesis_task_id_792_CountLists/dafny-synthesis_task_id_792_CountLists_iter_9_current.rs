use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn CountLists(lists: Seq<Seq<int>>) -> (count: nat)
    ensures
        count == lists.len()
{
    lists.len() as nat
}

}