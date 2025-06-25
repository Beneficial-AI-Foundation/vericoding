// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn Interleave(s1: Seq<int>, s2: Seq<int>, s3: Seq<int>) -> (r: Seq<int>)
    requires s1.len() == s2.len() and s2.len() == s3.len()
    ensures r.len() == 3 * s1.len(),
            forall|i: int| 0 <= i < s1.len() ==> r[3*i] == s1[i] and r[3*i + 1] == s2[i] and r[3*i + 2] == s3[i]
{
}

}