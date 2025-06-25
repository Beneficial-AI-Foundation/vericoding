// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn DeepCopySeq(s: Seq<int>) -> (copy: Seq<int>)
    ensures copy.len() == s.len(),
            forall|i: int| 0 <= i < s.len() ==> copy[i] == s[i]
{
}

}