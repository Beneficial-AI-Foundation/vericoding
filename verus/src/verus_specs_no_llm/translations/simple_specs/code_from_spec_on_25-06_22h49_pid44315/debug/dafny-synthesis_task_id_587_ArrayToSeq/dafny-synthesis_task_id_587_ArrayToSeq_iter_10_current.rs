use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn ArrayToSeq(a: Vec<i32>) -> (s: Seq<i32>)
    ensures
        s.len() == a@.len(),
        forall|i: int| 0 <= i < a@.len() ==> s[i] == a@[i]
{
    // Convert the vector to a sequence by returning its view
    // The view of a Vec<T> is Seq<T>, so this should work
    a@
}

}