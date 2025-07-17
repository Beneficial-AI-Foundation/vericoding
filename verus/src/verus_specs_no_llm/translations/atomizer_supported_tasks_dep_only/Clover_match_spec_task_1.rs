// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_Match(s: String, p: String) -> b: bool
    requires
        s.len() == p.len()
    ensures
        b <==> forall |n: int| 0 <= n < s.len() ==> s.index(n) == p.index(n) || p.index(n) == '?'
;

proof fn lemma_Match(s: String, p: String) -> (b: bool)
    requires
        s.len() == p.len()
    ensures
        b <==> forall |n: int| 0 <= n < s.len() ==> s.index(n) == p.index(n) || p.index(n) == '?'
{
    false
}

}