// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn FindSmallest(s: Vec<int>) -> (min: int)
    requires s.len() > 0
    ensures forall|i: int| 0 <= i < s.len() ==> min <= s[i],
            exists|i: int| 0 <= i < s.len() and min == s[i]
{
}

}