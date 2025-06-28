// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn FindFirstRepeatedChar(s: String) -> (found: bool, c: char)
    ensures
        found ==> exists i, j :: 0 <= i < j < s.len() && s.spec_index(i) == s.spec_index(j) && s.spec_index(i) == c && (forall k, l :: 0 <= k < l < j && s.spec_index(k) == s.spec_index(l) ==> k >= i),
        !found ==> (forall i, j :: 0 <= i < j < s.len() ==> s.spec_index(i) != s.spec_index(j))
{
    return (false, '\0');
}

}