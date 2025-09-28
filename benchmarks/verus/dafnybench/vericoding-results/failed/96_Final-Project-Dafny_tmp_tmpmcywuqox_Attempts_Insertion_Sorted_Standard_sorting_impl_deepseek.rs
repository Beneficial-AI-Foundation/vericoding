use vstd::prelude::*;

verus! {

spec fn insertion_sorted(array: Seq<int>, left: int, right: int) -> bool
    recommends 0 <= left <= right <= array.len()
{
    forall|i: int, j: int| left <= i < j < right ==> array[i] <= array[j]
}

// <vc-helpers>
spec fn sorted_range(a: Seq<int>, l: int, r: int) -> bool
    recommends 0 <= l <= r <= a.len()
{
    forall|i: int, j: int| l <= i <= j < r ==> a[i] <= a[j]
}

proof fn lemma_insertion_sorted_implies_sorted_range(a: Seq<int>, l: int, r: int)
    requires insertion_sorted(a, l, r), 0 <= l <= r <= a.len()
    ensures sorted_range(a, l, r)
{
}

proof fn lemma_sorted_range_left(a: Seq<int>, l: int, m: int, r: int)
    requires sorted_range(a, l, r), l <= m <= r
    ensures sorted_range(a, l, m)
{
}

proof fn lemma_sorted_range_right(a: Seq<int>, l: int, m: int, r: int)
    requires sorted_range(a, l, r), l <= m <= r
    ensures sorted_range(a, m, r)
{
}

proof fn lemma_sorted_range_merge(a: Seq<int>, l: int, m: int, r: int)
    requires sorted_range(a, l, m), sorted_range(a, m, r), m < r ==> a[m-1] <= a[m]
    ensures sorted_range(a, l, r)
{
}

proof fn lemma_array_update_sorted_range(a: Seq<int>, i: int, v: int, l: int, r: int)
    requires 
        sorted_range(a, l, r),
        l <= i < r,
        (i > l ==> a[i-1] <= v),
        (i < r - 1 ==> v <= a[i+1])
    ensures sorted_range(a.update(i, v), l, r)
{
}

proof fn lemma_vec_len_unchanged<T>(v: &Vec<T>)
    ensures old(v)@.len() == v@.len()
{
}

proof fn lemma_seq_len_unchanged<T>(s: Seq<T>, idx: int, value: T)
    ensures s.update(idx, value).len() == s.len()
{
}

proof fn lemma_transitivity(a: int, b: int, c: int)
    requires a <= b, b <= c
    ensures a <= c
{
}
// </vc-helpers>

// <vc-spec>
fn sorting(array: &mut Vec<int>)
    requires old(array).len() > 1
    ensures insertion_sorted(array@, 0, array@.len() as int)
// </vc-spec>
// <vc-code>
{
    let n: usize = array.len();
    let mut i: usize = 1;
    
    while i < n
        invariant
            0 <= i <= n,
            sorted_range(array@, 0, i as int),
            array@.len() == old(array)@.len()
        decreases n - i
    {
        let key = array[i];
        let mut j: isize = i as isize - 1;
        
        while j >= 0
            invariant
                -1 <= j <= i as isize - 1,
                sorted_range(array@, 0, i as int),
// </vc-code>

fn main() {}

}