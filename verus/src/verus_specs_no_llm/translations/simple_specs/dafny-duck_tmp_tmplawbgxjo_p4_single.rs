// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_single(x: Vec<int>, y: Vec<int>) -> b:array<int>
    requires
        x.len() > 0,
        y.len() > 0
// ensuring that the new array is the two arrays joined
    ensures
        b.index(..) == x.index(..) + y.index(..)
;

proof fn lemma_single(x: Vec<int>, y: Vec<int>) -> (b: Vec<int>)
    requires
        x.len() > 0,
        y.len() > 0
// ensuring that the new array is the two arrays joined
    ensures
        b.index(..) == x.index(..) + y.index(..)
{
    Vec::new()
}

}