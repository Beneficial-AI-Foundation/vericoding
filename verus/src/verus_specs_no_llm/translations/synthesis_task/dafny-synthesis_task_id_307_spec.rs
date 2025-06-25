// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn main() {
}

fn DeepCopySeq(s: Seq<int>) -> (copy: Seq<int>)
    ensures
        copy.len() == s.len(),
        forall i :: 0 <= i < s.len() ==> copy.spec_index(i) == s.spec_index(i)
{
    return Seq::empty();
}

}