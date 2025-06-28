// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn IsSpaceCommaDot(c: char) -> bool {
    c == ' ' | c == ',' .len()| c == '.'
}

fn ReplaceWithColon(s: String) -> (v: String)
    ensures
        v.len() == s.len(),
        forall i :: 0 <= i < s.len() ==> (IsSpaceCommaDot(s.spec_index(i)) ==> v.spec_index(i) == ':') && (!IsSpaceCommaDot(s.spec_index(i)) ==> v.spec_index(i) == s.spec_index(i))
{
    return String::new();
}

}