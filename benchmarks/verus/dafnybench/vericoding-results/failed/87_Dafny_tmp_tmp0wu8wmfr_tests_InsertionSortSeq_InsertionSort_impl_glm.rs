use vstd::prelude::*;

verus! {

// Insertion sort.
//
// Author: Snorri Agnarsson, snorri@hi.is


spec fn is_sorted(s: Seq<int>) -> bool {
    forall|p: int, q: int| 0 <= p < q < s.len() ==> s[p] <= s[q]
}

// <vc-helpers>
fn insert_into_sorted(s: Seq<int>, x: int) -> (r: Seq<int>)
    requires is_sorted(s)
    ensures is_sorted(r),
    ensures r.to_multiset() == s.to_multiset() + Multiset::singleton(x)
    decreases s.len(),
{
    if s.len() == 0 {
        seq![x]
    } else {
        if x <= s[0] {
            seq![x] + s
        } else {
            let tail = s.drop(1);
            let inserted_tail = insert_into_sorted(tail, x);
            proof {
                assert(s.to_multiset() == Multiset::singleton(s[0]) + tail.to_multiset());
            }
            seq![s[0]] + inserted_tail
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn insertion_sort(s: Seq<int>) -> (r: Seq<int>)
    ensures
        s.to_multiset() == r.to_multiset(),
        is_sorted(r),
// </vc-spec>
// <vc-code>
{
    let mut result: Seq<int> = seq![];
    let mut i: int = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            is_sorted(result),
            result.to_multiset() == s.take(i).to_multiset(),
    {
        let x = s[i];
        result = insert_into_sorted(result, x);
        i += 1;
    }
    proof {
        assert(s.take(s.len()) =~= s);
    }
    result
}
// </vc-code>

fn main() {}

}