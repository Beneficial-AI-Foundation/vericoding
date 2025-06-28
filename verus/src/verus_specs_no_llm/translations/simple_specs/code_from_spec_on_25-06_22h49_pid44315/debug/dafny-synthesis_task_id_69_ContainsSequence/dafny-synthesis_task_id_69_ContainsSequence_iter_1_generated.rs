use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn ContainsSequence(list: Seq<Seq<int>>, sub: Seq<int>) -> (result: bool)
    ensures
        result <==> (exists i :: 0 <= i < list.len() && sub == list.spec_index(i))
{
    let mut i = 0;
    while i < list.len()
        invariant
            0 <= i <= list.len(),
            forall j :: 0 <= j < i ==> sub != list.spec_index(j),
    {
        if sub == list.spec_index(i) {
            return true;
        }
        i = i + 1;
    }
    return false;
}

}