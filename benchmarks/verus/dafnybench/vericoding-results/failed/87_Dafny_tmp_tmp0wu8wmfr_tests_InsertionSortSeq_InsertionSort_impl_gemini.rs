// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_sorted(s: Seq<int>) -> bool {
    forall|p: int, q: int| 0 <= p < q < s.len() ==> s[p] <= s[q]
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added proof body to lemma_sorted_subrange */
spec fn insert(s: Seq<int>, v: int) -> Seq<int>
    decreases s.len()
{
    if s.len() == 0 {
        seq![v]
    } else if v <= s[0] {
        seq![v] + s
    } else {
        seq![s[0]] + insert(s.subrange(1, s.len() as int), v)
    }
}

proof fn lemma_sorted_subrange(s: Seq<int>, i: int, j: int)
    requires
        is_sorted(s),
        0 <= i <= j <= s.len(),
    ensures is_sorted(s.subrange(i, j))
{
    forall|p: int, q: int|
        requires 0 <= p < q < s.subrange(i, j).len()
        ensures s.subrange(i, j)[p] <= s.subrange(i, j)[q]
    {
    }
}

proof fn lemma_insert_properties(s: Seq<int>, v: int)
    requires is_sorted(s),
    ensures
        is_sorted(insert(s, v)),
        insert(s, v).to_multiset() == s.to_multiset().insert(v),
    decreases s.len(),
{
    if s.len() > 0 && v > s[0] {
        lemma_sorted_subrange(s, 1, s.len() as int);
        let tail = s.subrange(1, s.len() as int);
        lemma_insert_properties(tail, v);
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
/* code modified by LLM (iteration 5): moved ghost loop to proof block and fixed lemma path */
{
    proof {
        let mut sorted_s = Seq::<int>::empty();
        let mut i: nat = 0;
        while i < s.len()
            invariant
                0 <= i <= s.len(),
                is_sorted(sorted_s),
                sorted_s.to_multiset() == s.subrange(0, i as int).to_multiset(),
            decreases s.len() - i
        {
            lemma_insert_properties(sorted_s, s[i as int]);
            sorted_s = insert(sorted_s, s[i as int]);
            i = i + 1;
        }

        vstd::seq::lemma_subrange_is_full_range(s, 0, s.len() as int);
        sorted_s
    }
}
// </vc-code>

}
fn main() {}