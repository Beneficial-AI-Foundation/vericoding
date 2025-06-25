// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn ReplaceBlanksWithChar(s: String, ch: char) -> (v: String)
    ensures v.len() == s.len(),
            forall|i: int| 0 <= i < s.len() ==> (s[i] == ' ' ==> v[i] == ch) and (s[i] != ' ' ==> v[i] == s[i])
{
}

}