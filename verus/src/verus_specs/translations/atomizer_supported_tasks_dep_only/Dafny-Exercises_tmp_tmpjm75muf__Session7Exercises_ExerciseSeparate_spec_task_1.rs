use vstd::prelude::*;

verus! {

spec fn strictNegative(v: &[i32], i: int, j: int) -> bool
    recommends 0 <= i <= j <= v.len()
{
    forall|u: int| i <= u < j ==> v[u as usize] < 0
}

spec fn positive(s: Seq<i32>) -> bool {
    forall|u: int| 0 <= u < s.len() ==> s[u] >= 0
}

spec fn isPermutation(s: Seq<i32>, t: Seq<i32>) -> bool {
    s.to_multiset() == t.to_multiset()
}

pub fn separate(v: &mut Vec<i32>) -> (i: usize)
    requires(
        old(v).len() <= usize::MAX
    )
    ensures(
        0 <= i <= v.len() &&
        positive(v@.subrange(0, i as int)) &&
        strictNegative(v.as_slice(), i as int, v.len() as int) &&
        isPermutation(v@, old(v)@)
    )
{
}

}