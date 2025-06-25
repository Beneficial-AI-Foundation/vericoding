// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn MinSecondValueFirst(s: Vec<Seq<int>>) -> (firstOfMinSecond: int)
    requires s.len() > 0,
             forall|i: int| 0 <= i < s.len() ==> s[i].len() >= 2
    ensures exists|i: int| 0 <= i < s.len() and firstOfMinSecond == s[i][0] and 
        (forall|j: int| 0 <= j < s.len() ==> s[i][1] <= s[j][1])
{
}

}