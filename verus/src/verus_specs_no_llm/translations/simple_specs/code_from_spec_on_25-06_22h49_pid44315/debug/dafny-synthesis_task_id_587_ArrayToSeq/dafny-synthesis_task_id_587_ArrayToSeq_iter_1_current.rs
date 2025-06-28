use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn ArrayToSeq(a: Vec<int>) -> (s: Seq<int>)
    ensures
        s.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> s.spec_index(i) == a.spec_index(i)
{
    a.to_seq()
}

}