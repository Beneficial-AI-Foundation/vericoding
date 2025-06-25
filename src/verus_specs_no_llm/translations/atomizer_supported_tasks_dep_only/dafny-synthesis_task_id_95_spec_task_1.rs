// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn SmallestListLength(s: Seq<Seq<int>>) -> (v: int)
    requires s.len() > 0
    ensures forall|i: int| 0 <= i < s.len() ==> v <= s[i].len(),
            exists|i: int| 0 <= i < s.len() and v == s[i].len()
{
}

}