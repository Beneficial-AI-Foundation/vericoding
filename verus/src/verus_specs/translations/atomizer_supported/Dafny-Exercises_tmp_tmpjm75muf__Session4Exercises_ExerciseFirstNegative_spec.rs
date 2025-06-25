use vstd::prelude::*;

verus! {

// ATOM 
spec fn positive(s: Seq<int>) -> bool
{
    forall|u: int| 0 <= u < s.len() ==> s[u] >= 0
}

// SPEC 
pub fn mfirstNegative(v: &[int]) -> (b: bool, i: int)
    ensures
        b <==> exists|k: int| 0 <= k < v.len() && v[k] < 0,
        b ==> 0 <= i < v.len() && v[i] < 0 && positive(v.subrange(0, i)),
{
}

// SPEC 
pub fn mfirstNegative2(v: &[int]) -> (b: bool, i: int)
    ensures
        b <==> exists|k: int| 0 <= k < v.len() && v[k] < 0,
        b ==> 0 <= i < v.len() && v[i] < 0 && positive(v.subrange(0, i)),
{
}

}