// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn allEqual(s: Seq<int>) -> bool {
    forall |i: int, j: int|0<=i<s.len() && 0<=j<s.len() ==> s.index(i)==s.index(j)
}

spec fn spec_mallEqual5(v: Vec<int>) -> b:bool
    ensures
        b==allEqual(v.index(0..v.len()))
;

proof fn lemma_mallEqual5(v: Vec<int>) -> (b: bool)
    ensures
        b==allEqual(v.index(0..v.len()))
{
    false
}

}