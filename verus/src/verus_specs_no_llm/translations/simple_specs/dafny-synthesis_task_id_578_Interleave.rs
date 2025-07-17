// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_Interleave(s1: Seq<int>, s2: Seq<int>, s3: Seq<int>) -> r: seq<int>
    requires
        s1.len() == s2.len() && s2.len() == s3.len()
    ensures
        r.len() == 3 * s1.len(),
        forall |i: int| 0 <= i < s1.len() ==> r.index(3*i) == s1.index(i) && r.index(3*i + 1) == s2.index(i) && r.index(3*i + 2) == s3.index(i)
;

proof fn lemma_Interleave(s1: Seq<int>, s2: Seq<int>, s3: Seq<int>) -> (r: Seq<int>)
    requires
        s1.len() == s2.len() && s2.len() == s3.len()
    ensures
        r.len() == 3 * s1.len(),
        forall |i: int| 0 <= i < s1.len() ==> r.index(3*i) == s1.index(i) && r.index(3*i + 1) == s2.index(i) && r.index(3*i + 2) == s3.index(i)
{
    Seq::empty()
}

}