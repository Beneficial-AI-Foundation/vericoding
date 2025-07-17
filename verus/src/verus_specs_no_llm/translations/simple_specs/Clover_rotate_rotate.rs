// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_rotate(a: Vec<int>, offset: int) -> b: array<int>
    requires
        0<=offset
    ensures
        b.len()==a.len(),
        forall |i: int|0<=i<a.len() ==> b.index(i)==a.index((i+offset)%a.len())
;

proof fn lemma_rotate(a: Vec<int>, offset: int) -> (b: Vec<int>)
    requires
        0<=offset
    ensures
        b.len()==a.len(),
        forall |i: int|0<=i<a.len() ==> b.index(i)==a.index((i+offset)%a.len())
{
    Vec::new()
}

}