// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_BitwiseXOR(a: Seq<u32>, b: Seq<u32>) -> result: seq<bv32>
    requires
        a.len() == b.len()
    ensures
        result.len() == a.len(),
        forall |i: int| 0 <= i < result.len() ==> result.index(i) == a.index(i) ^ b.index(i)
;

proof fn lemma_BitwiseXOR(a: Seq<u32>, b: Seq<u32>) -> (result: Seq<u32>)
    requires
        a.len() == b.len()
    ensures
        result.len() == a.len(),
        forall |i: int| 0 <= i < result.len() ==> result.index(i) == a.index(i) ^ b.index(i)
{
    Seq::empty()
}

}