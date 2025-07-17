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
        a == old(a),
        b.len() == a.len(),
        forall |i: int| 0 <= i < a.len() ==> b.index(i) == a.index(a.len() - i - 1)
;

proof fn lemma_Reverse(a: Vec<char>) -> (b: Vec<char>)
    requires
        a.len() > 0
    ensures
        a == old(a),
        b.len() == a.len(),
        forall |i: int| 0 <= i < a.len() ==> b.index(i) == a.index(a.len() - i - 1)
{
    Vec::new()
}

}