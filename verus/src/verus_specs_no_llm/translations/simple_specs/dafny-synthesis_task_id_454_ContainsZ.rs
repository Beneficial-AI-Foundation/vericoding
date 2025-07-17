// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_ContainsZ(s: String) -> result: bool
    ensures
        result <==> (exists |i: int| 0 <= i < s.len() && (s.index(i) == 'z' || s.index(i) == 'Z'))
;

proof fn lemma_ContainsZ(s: String) -> (result: bool)
    ensures
        result <==> (exists |i: int| 0 <= i < s.len() && (s.index(i) == 'z' || s.index(i) == 'Z'))
{
    false
}

}