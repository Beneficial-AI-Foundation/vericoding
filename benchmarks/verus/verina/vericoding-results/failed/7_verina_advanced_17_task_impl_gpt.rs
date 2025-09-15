// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn sorted(s: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] <= s[j]
}

spec fn swap_seq(s: Seq<i32>, i: int, j: int) -> Seq<i32>
    recommends 0 <= i < s.len(), 0 <= j < s.len()
{
    s.update(i, s[j]).update(j, s[i])
}

proof fn swap_preserves_multiset(s: Seq<i32>, i: int, j: int)
    requires 0 <= i < s.len(), 0 <= j < s.len()
    ensures swap_seq(s, i, j).to_multiset() == s.to_multiset()
{
}

proof fn sorted_subrange(s: Seq<i32>, a: int, b: int)
    requires 0 <= a <= b <= s.len(), sorted(s)
    ensures sorted(s.subrange(a, b))
{
}
// </vc-helpers>

// <vc-spec>
fn insertion_sort(l: Vec<i32>) -> (result: Vec<i32>)
    ensures

        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] <= result[j],

        result@.to_multiset() == l@.to_multiset(),
// </vc-spec>
// <vc-code>
{
    let mut r: Vec<i32> = Vec::new();

    let mut i: usize = 0;
    while i < l.len()
        invariant
            i <= l.len(),
            r.len() == i,
            sorted(r@),
            r@.to_multiset() == l@.subrange(0, i as int).to_multiset()
    {
        let x = l[i];

        // find insertion position
        let mut pos: usize = 0;
        while pos < r.len() && r[pos] <= x
            invariant
                pos <= r.len(),
                r.len() == i,
                sorted(r@),
                forall|k: int| 0 <= k < pos as int ==> r@[k] <= x
        {
            pos += 1;
        }

        // append x, then bubble it left to position pos
        r.push(x);

        let mut k: usize = r.len() - 1;
        while k > pos
            invariant
                pos < r.len(),
                r.len() == i + 1,
                r@.to_multiset() == (l@.subrange(0, i as int) + seq![x]).to_multiset()
        {
            r.swap(k - 1, k);
            k -= 1;
        }

        i += 1;
    }

    r
}
// </vc-code>

}
fn main() {}