// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn ReplaceChars(s: String, oldChar: char, newChar: char) -> (v: String)
    ensures v.len() == s.len(),
            forall|i: int| 0 <= i < s.len() ==> (s[i] == oldChar ==> v[i] == newChar) and (s[i] != oldChar ==> v[i] == s[i])
{
}

}