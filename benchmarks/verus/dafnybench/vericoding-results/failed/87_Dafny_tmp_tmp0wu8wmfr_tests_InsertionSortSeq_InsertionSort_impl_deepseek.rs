use vstd::prelude::*;

verus! {

// Insertion sort.
//
// Author: Snorri Agnarsson, snorri@hi.is


spec fn is_sorted(s: Seq<int>) -> bool {
    forall|p: int, q: int| 0 <= p < q < s.len() ==> s[p] <= s[q]
}

// <vc-helpers>
spec fn insert(n: int, s: Seq<int>) -> Seq<int> {
    if s.len() == 0 {
        Seq::new(1, |i| n)
    } else if n <= s[0] {
        s.insert(0, n)
    } else {
        Seq::new(1, |i| s[0]).add(insert(n, s.subrange(1, s.len() as int)))
    }
}

spec fn insertion_sort_spec(s: Seq<int>) -> Seq<int> {
    decreases(s.len());
    if s.len() == 0 {
        s
    } else {
        insert(s[0], insertion_sort_spec(s.subrange(1, s.len() as int)))
    }
}

proof fn lemma_insert_preserves_multiset(n: int, s: Seq<int>)
    ensures
        insert(n, s).to_multiset() == s.to_multiset().insert(n),
{
    reveal(insert);
    if s.len() > 0 {
        if n <= s[0] {
        } else {
            lemma_insert_preserves_multiset(n, s.subrange(1, s.len() as int));
        }
    }
}

proof fn lemma_insert_sorted(n: int, s: Seq<int>)
    requires
        is_sorted(s),
    ensures
        is_sorted(insert(n, s)),
{
    reveal(insert);
    if s.len() > 0 {
        if n <= s[0] {
        } else {
            lemma_insert_sorted(n, s.subrange(1, s.len() as int));
        }
    }
}

proof fn lemma_insertion_sort_spec_multiset(s: Seq<int>)
    ensures
        s.to_multiset() == insertion_sort_spec(s).to_multiset(),
    decreases(s.len()),
{
    reveal(insertion_sort_spec);
    if s.len() > 0 {
        lemma_insertion_sort_spec_multiset(s.subrange(1, s.len() as int));
        lemma_insert_preserves_multiset(s[0], insertion_sort_spec(s.subrange(1, s.len() as int)));
    }
}

proof fn lemma_insertion_sort_spec_sorted(s: Seq<int>)
    ensures
        is_sorted(insertion_sort_spec(s)),
    decreases(s.len()),
{
    reveal(insertion_sort_spec);
    if s.len() > 0 {
        lemma_insertion_sort_spec_sorted(s.subrange(1, s.len() as int));
        lemma_insert_sorted(s[0], insertion_sort_spec(s.subrange(1, s.len() as int)));
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
    let mut result = Seq::empty();
    let mut i: nat = 0;
    while i < s.len()
        invariant
            i <= s.len(),
            result.to_multiset() == s.subrange(0, i as int).to_multiset(),
            is_sorted(result),
    {
        let idx: int = i as int;
        let elem = s[idx];
        let mut j: nat = 0;
        while j < result.len()
            invariant
                j <= result.len(),
                forall|k: nat| k < j ==> result[k as int] < elem,
        {
            let j_idx: int = j as int;
            if result[j_idx] < elem {
                j = j + 1;
            } else {
                break;
            }
        }
        let j_final: int = j as int;
        result = result.insert(j_final, elem);
        i = i + 1;
    }
    result
}
// </vc-code>

fn main() {}

}