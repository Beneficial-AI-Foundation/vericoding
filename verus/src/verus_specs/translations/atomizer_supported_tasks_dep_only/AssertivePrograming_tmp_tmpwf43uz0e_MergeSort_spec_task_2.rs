use vstd::prelude::*;

spec fn sorted(q: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i <= j < q.len() ==> q[i] <= q[j]
}

pub fn merge(b: &mut Vec<int>, c: &Vec<int>, d: &Vec<int>)
    requires(
        old(b).len() == c.len() + d.len() &&
        sorted(c@) && sorted(d@)
    )
    ensures(
        sorted(b@) && 
        b@.to_multiset() == c@.to_multiset() + d@.to_multiset()
    )
{
}

pub fn merge_loop(b: &mut Vec<int>, c: &Vec<int>, d: &Vec<int>, i0: usize, j0: usize) -> (i: usize, j: usize)
    requires(
        old(b).len() == c.len() + d.len() &&
        sorted(c@) && sorted(d@) &&
        i0 <= c.len() && j0 <= d.len() && i0 + j0 <= old(b).len() &&
        inv_sub_set(old(b)@, c@, d@, i0, j0) &&
        inv_sorted(old(b)@, c@, d@, i0, j0) &&
        i0 + j0 < old(b).len()
    )
    ensures(
        i <= c.len() && j <= d.len() && i + j <= b.len() &&
        inv_sub_set(b@, c@, d@, i, j) &&
        inv_sorted(b@, c@, d@, i, j) &&
        (0 <= c.len() - i < c.len() - i0 || (c.len() - i == c.len() - i0 && 0 <= d.len() - j < d.len() - j0))
    )
{
}

spec fn inv_sorted(b: Seq<int>, c: Seq<int>, d: Seq<int>, i: usize, j: usize) -> bool;

spec fn inv_sub_set(b: Seq<int>, c: Seq<int>, d: Seq<int>, i: usize, j: usize) -> bool;

proof fn lemma_multisets_equals(b: Seq<int>, c: Seq<int>, d: Seq<int>, i: usize, j: usize)
    requires(
        i == c.len() &&
        j == d.len() &&
        i + j == b.len() &&
        b.subrange(0, i + j as int).to_multiset() == c.subrange(0, i as int).to_multiset() + d.subrange(0, j as int).to_multiset()
    )
    ensures(
        b.to_multiset() == c.to_multiset() + d.to_multiset()
    )
{
}

proof fn lemma_inv_subset_take_value_from_c(b: Seq<int>, c: Seq<int>, d: Seq<int>, i: usize, j: usize);

proof fn lemma_inv_subset_take_value_from_d(b: Seq<int>, c: Seq<int>, d: Seq<int>, i: usize, j: usize)
    requires(
        i <= c.len() &&
        j < d.len() &&
        i + j < b.len() &&
        c.len() + d.len() == b.len() &&
        b.subrange(0, i + j as int).to_multiset() == c.subrange(0, i as int).to_multiset() + d.subrange(0, j as int).to_multiset() &&
        b[i + j as int] == d[j as int]
    )
    ensures(
        b.subrange(0, i + j + 1 as int).to_multiset() == c.subrange(0, i as int).to_multiset() + d.subrange(0, j + 1 as int).to_multiset()
    )
{
}