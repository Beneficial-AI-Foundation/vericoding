// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn SplitStringIntoChars(s: String) -> (v: Seq<char>)
    ensures v.len() == s.len(),
            forall|i: int| 0 <= i < s.len() ==> v[i] == s[i]
{
}

}