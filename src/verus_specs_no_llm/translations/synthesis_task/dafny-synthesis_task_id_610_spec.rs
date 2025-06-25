// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn RemoveElement(s: Vec<int>, k: int) -> (v: Vec<int>)
    requires 0 <= k < s.len()
    ensures v.len() == s.len() - 1,
            forall|i: int| 0 <= i < k ==> v[i] == s[i],
            forall|i: int| k <= i < v.len() ==> v[i] == s[i + 1]
{
}

}