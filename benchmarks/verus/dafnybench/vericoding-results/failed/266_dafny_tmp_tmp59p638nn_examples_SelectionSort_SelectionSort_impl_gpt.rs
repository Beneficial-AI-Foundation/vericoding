use vstd::prelude::*;

verus! {

spec fn ordered(a: Seq<int>, left: int, right: int) -> bool {
    &&& 0 <= left <= right <= a.len()
    &&& forall |i: int| #![trigger a[i]] left < i < right ==> a[i-1] <= a[i]
}

// <vc-helpers>
proof fn ordered_from_pairwise(a: Seq<int>, n: int)
    requires
        0 <= n <= a.len(),
        forall |t: int| 0 < t && t < n ==> a[t - 1] <= a[t]
    ensures
        ordered(a, 0, n)
{
    assert(0 <= 0 <= n <= a.len());
    assert(forall |i: int| #![trigger a[i]] 0 < i && i < n ==> a[i - 1] <= a[i]);
    assert(ordered(a, 0, n));
}
// </vc-helpers>

// <vc-spec>
fn selection_sort(a: &mut Vec<int>)
    ensures 
        ordered(a@, 0, a.len() as int),
        a.len() == old(a).len(),
        a@.to_multiset() =~= old(a)@.to_multiset(),
// </vc-spec>
// <vc-code>
{
    let n = a.len();
    let ghost old_seq = a@;

    let mut i: usize = 0;
    while i < n
        invariant
            a.len() == n,
            i <= n,
            forall |t: int| 0 < t && t < i as int ==> a@[t - 1] <= a@[t],
            forall |k: int, j2: int|
                0 <= k && k < i as int && i as int <= j2 && j2 < n as int ==> #[trigger] a@[j2] >= a@[k],
            a@.to_multiset() =~= old_seq.to_multiset()
        decreases n - i
    {
        let mut m: usize = i;
        let mut j: usize = i + 1;
        while j < n
            invariant
                a.len() == n,
                i < n,
                i <= m && m < j,
                i < j && j <= n,
                forall |k: int| i as int <= k && k < j as int ==> a@[m as int] <= a@[k],
                forall |t: int| 0 < t && t < i as int ==> a@[t - 1] <= a@[t],
                forall |kk: int, jj: int|
                    0 <= kk && kk < i as int && i as int <= jj && jj < n as int ==> #[trigger] a@[jj] >= a@[kk],
                a@.to_multiset() =~= old_seq.to_multiset()
            decreases n - j
        {
            if a[j] < a[m] {
                m = j;
            }
            j = j + 1;
        }

        let ghost pre = a@;

        a.swap(i, m);

        proof {
            assert_forall_by(|t: int| {
                requires 0 < t && t < i as int + 1
// </vc-code>

fn main() {}

}