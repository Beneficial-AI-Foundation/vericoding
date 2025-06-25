// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn RemoveChars(s1: String, s2: String) -> (v: String)
    ensures v.len() <= s1.len(),
            forall|i: int| 0 <= i < v.len() ==> (v[i] in s1) and !(v[i] in s2),
            forall|i: int| 0 <= i < s1.len() ==> (s1[i] in s2) or (s1[i] in v)
{
}

}