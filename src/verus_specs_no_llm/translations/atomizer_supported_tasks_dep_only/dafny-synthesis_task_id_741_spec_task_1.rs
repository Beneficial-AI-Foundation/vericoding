// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn AllCharactersSame(s: String) -> (result: bool)
    ensures result ==> forall|i: int, j: int| 0 <= i < s.len() and 0 <= j < s.len() ==> s[i] == s[j],
            !result ==> (s.len() > 1) and (exists|i: int, j: int| 0 <= i < s.len() and 0 <= j < s.len() and i != j and s[i] != s[j])
{
}

}