// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_CubeElements(a: Vec<int>) -> cubed: array<int>
    ensures
        cubed.len() == a.len(),
        forall |i: int| 0 <= i < a.len() ==> cubed.index(i) == a.index(i) * a.index(i) * a.index(i)
;

proof fn lemma_CubeElements(a: Vec<int>) -> (cubed: Vec<int>)
    ensures
        cubed.len() == a.len(),
        forall |i: int| 0 <= i < a.len() ==> cubed.index(i) == a.index(i) * a.index(i) * a.index(i)
{
    Vec::new()
}

}