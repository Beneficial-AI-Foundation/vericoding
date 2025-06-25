// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

spec fn IsSpaceCommaDot(c: char) -> bool {
    c == ' ' | c == ',' .len()| c == '.'
}

fn ReplaceWithColon(s: String) -> (v: String)
    ensures v.len() == s.len(),
            forall|i: int| 0 <= i < s.len() ==> (IsSpaceCommaDot(s[i]) ==> v[i] == ':') and (!IsSpaceCommaDot(s[i]) ==> v[i] == s[i])
{
}

}