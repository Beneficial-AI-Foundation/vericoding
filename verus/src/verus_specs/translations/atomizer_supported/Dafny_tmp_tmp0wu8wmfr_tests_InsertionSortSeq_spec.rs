use vstd::prelude::*;

verus! {

spec fn is_sorted(s: Seq<int>) -> bool {
    forall|p: int, q: int| 0 <= p < q < s.len() ==> s[p] <= s[q]
}

pub fn insertion_sort(s: Seq<int>) -> (r: Seq<int>)
    ensures
        r.to_multiset() == s.to_multiset(),
        is_sorted(r),
{
}

}