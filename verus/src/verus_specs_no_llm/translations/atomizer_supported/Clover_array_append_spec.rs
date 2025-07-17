// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_append(a: Vec<int>, b: int) -> c:array<int>
    ensures
        a.index(..) + [b] == c.index(..)
;

proof fn lemma_append(a: Vec<int>, b: int) -> (c: Vec<int>)
    ensures
        a.index(..) + [b] == c.index(..)
{
    Vec::new()
}

}