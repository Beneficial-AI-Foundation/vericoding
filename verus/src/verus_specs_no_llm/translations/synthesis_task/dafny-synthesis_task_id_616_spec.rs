// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_ElementWiseModulo(a: Vec<int>, b: Vec<int>) -> result: array<int>
    requires
        a != null && b != null,
        a.len() == b.len(),
        forall |i: int| 0 <= i < b.len() ==> b.index(i) != 0
    ensures
        result != null,
        result.len() == a.len(),
        forall |i: int| 0 <= i < result.len() ==> result.index(i) == a.index(i) % b.index(i)
;

proof fn lemma_ElementWiseModulo(a: Vec<int>, b: Vec<int>) -> (result: Vec<int>)
    requires
        a != null && b != null,
        a.len() == b.len(),
        forall |i: int| 0 <= i < b.len() ==> b.index(i) != 0
    ensures
        result != null,
        result.len() == a.len(),
        forall |i: int| 0 <= i < result.len() ==> result.index(i) == a.index(i) % b.index(i)
{
    Vec::new()
}

}