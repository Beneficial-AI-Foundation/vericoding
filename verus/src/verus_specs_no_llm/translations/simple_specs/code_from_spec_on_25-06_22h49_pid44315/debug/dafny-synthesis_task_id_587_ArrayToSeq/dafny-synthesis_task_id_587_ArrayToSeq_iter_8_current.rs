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
    // In Verus, a Vec's view (@) is already a sequence
    // So we can simply return the view of the vector
    a@
}

}