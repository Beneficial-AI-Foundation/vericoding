// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_remove_front(a: Vec<int>) -> c:array<int>
    requires
        a.len()>0
    ensures
        a.index(1..) == c.index(..)
;

proof fn lemma_remove_front(a: Vec<int>) -> (c: Vec<int>)
    requires
        a.len()>0
    ensures
        a.index(1..) == c.index(..)
{
    Vec::new()
}

}