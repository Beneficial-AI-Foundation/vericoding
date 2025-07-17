// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_Reverse(a: Vec<char>) -> b: array<char>
    requires
        a.len() > 0
    ensures
        a.len() == b.len(),
        forall |x: int| 0 <= x < a.len() ==> b.index(x) == a.index(a.len() - x - 1)
;

proof fn lemma_Reverse(a: Vec<char>) -> (b: Vec<char>)
    requires
        a.len() > 0
    ensures
        a.len() == b.len(),
        forall |x: int| 0 <= x < a.len() ==> b.index(x) == a.index(a.len() - x - 1)
{
    Vec::new()
}

}