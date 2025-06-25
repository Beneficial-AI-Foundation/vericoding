// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn SmallestMissingNumber(s: Seq<int>) -> (v: int)
    requires forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] <= s[j],
             forall|i: int| 0 <= i < s.len() ==> s[i] >= 0
    ensures 0 <= v,
            v !in s,
            forall|k: int| 0 <= k < v ==> k in s
{
}

}