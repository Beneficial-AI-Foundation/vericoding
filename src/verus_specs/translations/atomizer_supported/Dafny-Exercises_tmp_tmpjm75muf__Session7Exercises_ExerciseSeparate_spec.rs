use vstd::prelude::*;

verus! {

spec fn strict_negative(v: &[int], i: int, j: int) -> bool
    recommends 0 <= i <= j <= v.len()
{
    forall|u: int| i <= u < j ==> v[u as usize] < 0
}

spec fn positive(s: Seq<int>) -> bool {
    forall|u: int| 0 <= u < s.len() ==> s[u] >= 0
}

spec fn is_permutation(s: Seq<int>, t: Seq<int>) -> bool {
    s.to_multiset() == t.to_multiset()
}

pub fn separate(v: &mut Vec<int>) -> (i: usize)
    ensures
        0 <= i <= v.len(),
        positive(v@.subrange(0, i as int)),
        strict_negative(v@.as_slice(), i as int, v.len() as int),
        is_permutation(v@, old(v)@),
{
}

}