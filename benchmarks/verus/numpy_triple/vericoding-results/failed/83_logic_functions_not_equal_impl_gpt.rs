// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn neq_seq<T: PartialEq>(s1: Seq<T>, s2: Seq<T>) -> Seq<bool>
    requires s1.len() == s2.len()
    ensures
        result.len() == s1.len(),
        forall|i: int| 0 <= i < s1.len() ==> result[i] == (s1[i] != s2[i]),
        (s1 == s2) ==> (forall|i: int| 0 <= i < s1.len() ==> result[i] == false),
        forall|i: int| 0 <= i < s1.len() ==> result[i] == (s2[i] != s1[i])
{
    Seq::new(s1.len(), |i: int| s1[i] != s2[i])
}
// </vc-helpers>

// <vc-spec>
fn numpy_not_equal<T: PartialEq>(x1: Vec<T>, x2: Vec<T>) -> (result: Vec<bool>)
    requires x1.len() == x2.len(),
    ensures
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == (x1[i] != x2[i]),

        (x1@ == x2@) ==> (forall|i: int| 0 <= i < result.len() ==> result[i] == false),

        forall|i: int| 0 <= i < result.len() ==> result[i] == (x2[i] != x1[i]),
// </vc-spec>
// <vc-code>
{
    let s = neq_seq::<T>(x1@, x2@);
    Vec::from_seq(s)
}
// </vc-code>

}
fn main() {}