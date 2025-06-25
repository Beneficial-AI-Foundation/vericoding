// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn ToCharArray(s: String) -> (a: Vec<char>)
    ensures a.len() == s.len(),
            forall|i: int| 0 <= i < s.len() ==> a[i] == s[i]
{
}

}