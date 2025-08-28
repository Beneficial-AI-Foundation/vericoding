use vstd::prelude::*;

verus! {

spec fn sorted(a: Seq<i32>, from: int, to: int) -> bool
    recommends 0 <= from <= to <= a.len()
{
    forall|u: int, v: int| from <= u < v < to ==> a[u] <= a[v]
}

spec fn pivot(a: Seq<i32>, to: int, pvt: int) -> bool
    recommends 0 <= pvt < to <= a.len()
{
    forall|u: int, v: int| 0 <= u < pvt < v < to ==> a[u] <= a[v]
}

// <vc-helpers>
spec fn sorted_range(a: Seq<i32>, i: int, j: int) -> bool
    recommends 0 <= i <= j <= a.len()
{
    forall|u: int, v: int| i <= u < v < j ==> a[u] <= a[v]
}

proof fn sorted_concat(a: Seq<i32>, i: int, j: int, k: int)
    requires
        0 <= i <= j <= k <= a.len(),
        sorted_range(a, i, j),
        sorted_range(a, j, k),
        (j < k ==> a[j-1] <= a[j]),
    ensures
        sorted_range(a, i, k)
{
    if i < k {
        reveal(forall|u: int, v: int| i <= u < v < k ==> a[u] <= a[v]);
        assert forall|u: int, v: int| i <= u < v < k implies a[u] <= a[v] by {
            if u < j && v >= j {
                assert(a[u] <= a[j-1]);
                if j < k {
                    assert(a[j-1] <= a[j]);
                    assert(a[j] <= a[v]);
                }
            }
        };
    }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn bubbleSort(a: &mut Vec<i32>)
    requires 
        old(a).len() > 0,
    ensures 
        sorted(a@, 0, a.len() as int),
        a@.to_multiset() == old(a)@.to_multiset(),
// </vc-spec>
// </vc-spec>

// <vc-code>
fn bubble_sort(a: &mut Vec<i32>)
    requires 
        old(a).len() > 0,
    ensures 
        sorted(a@, 0, a.len() as int),
        a@.to_multiset() == old(a)@.to_multiset(),
{
    let n = a.len();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            sorted_range(a@, 0, i as int),
            a@.to_multiset() == old(a)@.to_multiset(),
    {
        let mut j: usize = 0;
        while j < n - i - 1
            invariant
                0 <= i < n,
                0 <= j <= n - i - 1,
                sorted_range(a@, 0, i as int),
                forall|u: int| i <= u < j as int ==> a@[u] >= a@[j as int],
                a@.to_multiset() == old(a)@.to_multiset(),
        {
            if a[j] > a[j + 1] {
                a.swap(j, j + 1);
            }
            j = j + 1;
        }
        i = i + 1;
    }
}
// </vc-code>

fn main() {
}

}