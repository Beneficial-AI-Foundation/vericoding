use vstd::prelude::*;

verus! {

//ATOM
spec fn sorted(q: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i <= j < q.len() ==> q[i] <= q[j]
}

//SPEC
pub fn merge_sort(a: &[int]) -> (b: Vec<int>)
    ensures
        b.len() == a.len() && sorted(b@) && a@.to_multiset() == b@.to_multiset()
{
}

//ATOM
spec fn inv(a: Seq<int>, a1: Seq<int>, a2: Seq<int>, i: nat, mid: nat) -> bool {
    (i <= a1.len()) && (i <= a2.len()) && (i + mid <= a.len()) &&
    (a1.subrange(0, i as int) == a.subrange(0, i as int)) && (a2.subrange(0, i as int) == a.subrange(mid as int, (i + mid) as int))
}

//SPEC
pub fn merge(b: &mut [int], c: &[int], d: &[int])
    requires
        b.len() == c.len() + d.len(),
        sorted(c@) && sorted(d@)
    ensures
        sorted(b@) && b@.to_multiset() == c@.to_multiset() + d@.to_multiset()
{
}

//SPEC
pub fn merge_loop(b: &mut [int], c: &[int], d: &[int], i0: usize, j0: usize) -> (i: usize, j: usize)
    requires
        b.len() == c.len() + d.len(),
        sorted(c@) && sorted(d@),
        i0 <= c.len() && j0 <= d.len() && i0 + j0 <= b.len(),
        inv_sub_set(b@, c@, d@, i0, j0),
        inv_sorted(b@, c@, d@, i0, j0),
        i0 + j0 < b.len()
    ensures
        i <= c.len() && j <= d.len() && i + j <= b.len(),
        inv_sub_set(b@, c@, d@, i, j),
        inv_sorted(b@, c@, d@, i, j),
        0 <= c.len() - i < c.len() - i0 || (c.len() - i == c.len() - i0 && 0 <= d.len() - j < d.len() - j0)
{
}

//ATOM
spec fn inv_sorted(b: Seq<int>, c: Seq<int>, d: Seq<int>, i: nat, j: nat) -> bool {
    i <= c.len() && j <= d.len() && i + j <= b.len() &&
    ((i + j > 0 && i < c.len()) ==> (b[(j + i - 1) as int] <= c[i as int])) &&
    ((i + j > 0 && j < d.len()) ==> (b[(j + i - 1) as int] <= d[j as int])) &&
    sorted(b.subrange(0, (i + j) as int))
}

//ATOM
spec fn inv_sub_set(b: Seq<int>, c: Seq<int>, d: Seq<int>, i: nat, j: nat) -> bool {
    i <= c.len() && j <= d.len() && i + j <= b.len() &&
    b.subrange(0, (i + j) as int).to_multiset() == c.subrange(0, i as int).to_multiset() + d.subrange(0, j as int).to_multiset()
}

//SPEC
proof fn lemma_multisets_equals(b: Seq<int>, c: Seq<int>, d: Seq<int>, i: nat, j: nat)
    requires
        i == c.len(),
        j == d.len(),
        i + j == b.len(),
        b.subrange(0, (i + j) as int).to_multiset() == c.subrange(0, i as int).to_multiset() + d.subrange(0, j as int).to_multiset()
    ensures
        b.to_multiset() == c.to_multiset() + d.to_multiset()
{
}

//SPEC
proof fn lemma_inv_subset_take_value_from_c(b: Seq<int>, c: Seq<int>, d: Seq<int>, i: nat, j: nat)
    requires
        i < c.len(),
        j <= d.len(),
        i + j < b.len(),
        c.len() + d.len() == b.len(),
        b.subrange(0, (i + j) as int).to_multiset() == c.subrange(0, i as int).to_multiset() + d.subrange(0, j as int).to_multiset(),
        b[(i + j) as int] == c[i as int]
    ensures
        b.subrange(0, (i + j + 1) as int).to_multiset() == c.subrange(0, (i + 1) as int).to_multiset() + d.subrange(0, j as int).to_multiset()
{
}

//SPEC
proof fn lemma_inv_subset_take_value_from_d(b: Seq<int>, c: Seq<int>, d: Seq<int>, i: nat, j: nat)
    requires
        i <= c.len(),
        j < d.len(),
        i + j < b.len(),
        c.len() + d.len() == b.len(),
        b.subrange(0, (i + j) as int).to_multiset() == c.subrange(0, i as int).to_multiset() + d.subrange(0, j as int).to_multiset(),
        b[(i + j) as int] == d[j as int]
    ensures
        b.subrange(0, (i + j + 1) as int).to_multiset() == c.subrange(0, i as int).to_multiset() + d.subrange(0, (j + 1) as int).to_multiset()
{
}

//SPEC
pub fn main()
{
}

}