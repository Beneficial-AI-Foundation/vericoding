// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn FindFirstRepeatedChar(s: String) -> found: bool, c: char
    ensures found ==> exists|i: int, j: int| 0 <= i < j < s.len() and s[i] == s[j] and s[i] == c and (forall|k: int, l: int| 0 <= k < l < j and s[k] == s[l] ==> k >= i),
            !found ==> (forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] != s[j])
{
}

}