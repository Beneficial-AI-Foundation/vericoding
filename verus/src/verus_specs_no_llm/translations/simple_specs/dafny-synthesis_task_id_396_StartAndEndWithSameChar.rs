// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_StartAndEndWithSameChar(s: String) -> result: bool
    requires
        s.len() > 0
    ensures
        result <==> s.index(0) == s.index(s.len() - 1)
;

proof fn lemma_StartAndEndWithSameChar(s: String) -> (result: bool)
    requires
        s.len() > 0
    ensures
        result <==> s.index(0) == s.index(s.len() - 1)
{
    false
}

}