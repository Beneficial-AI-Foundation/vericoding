use vstd::prelude::*;

verus! {

spec fn strict_sorted(s: Seq<i32>) -> bool {
    forall|u: int, w: int| 0 <= u < w < s.len() ==> s[u] < s[w]
}

// <vc-helpers>
spec fn contained_in_range(x: i32, w: Seq<i32>, start: int, end: int) -> bool {
    exists|i: int| start <= i < end && w[i] == x
}

proof fn lemma_strict_sorted_contains(x: i32, w: Seq<i32>, start: int, end: int)
    requires
        strict_sorted(w),
        0 <= start <= end <= w.len(),
    ensures
        contained_in_range(x, w, start, end) == (exists|i: int| start <= i < end && w[i] == x)
{
}

proof fn lemma_strict_sorted_monotonic(w: Seq<i32>, i: int, j: int)
    requires
        strict_sorted(w),
        0 <= i < j < w.len(),
    ensures
        w[i] < w[j],
{
}

spec fn binary_search_spec(w: Seq<i32>, x: i32, low: int, high: int) -> (idx: int)
    recommends
        strict_sorted(w),
        0 <= low <= high <= w.len(),
    ensures
        low <= idx <= high,
        forall|i: int| low <= i < idx ==> w[i] < x,
        forall|i: int| idx <= i < high ==> w[i] >= x,
{
    if low >= high {
        low
    } else {
        let mid = low + (high - low) / 2;
        if w[mid] < x {
            binary_search_spec(w, x, mid + 1, high)
        } else {
            binary_search_spec(w, x, low, mid)
        }
    }
}

proof fn lemma_binary_search_correct(w: Seq<i32>, x: i32, low: int, high: int)
    requires
        strict_sorted(w),
        0 <= low <= high <= w.len(),
    ensures
        let idx = binary_search_spec(w, x, low, high);
        low <= idx <= high,
        forall|i: int| low <= i < idx ==> w[i] < x,
        forall|i: int| idx <= i < high ==> w[i] >= x,
{
    if low >= high {
    } else {
        let mid = low + (high - low) / 2;
        if w[mid] < x {
            lemma_binary_search_correct(w, x, mid + 1, high);
        } else {
            lemma_binary_search_correct(w, x, low, mid);
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn mcontained(v: &[i32], w: &[i32], n: usize, m: usize) -> (b: bool)
//Specify and implement an O(m+n) algorithm that returns b
//v and w are strictly increasing ordered arrays
//b is true iff the first n elements of v are contained in the first m elements of w
    requires 
        n <= m,
        n >= 0,
        strict_sorted(v@),
        strict_sorted(w@),
        v@.len() >= n,
        w@.len() >= m,
    ensures
        b == forall|k: int| 0 <= k < n ==> w@.subrange(0, m as int).contains(v@[k])
// </vc-spec>
// <vc-code>
{
    let mut i: usize = 0;
    let mut j: usize = 0;
    
    while i < n && j < m
        invariant
            0 <= i <= n,
            0 <= j <= m,
            forall|k: int| 0 <= k < i ==> contained_in_range(v@[k], w@, 0, j as int),
        decreases
            (m - j) + (n - i),
    {
        if v[i] == w[j] {
            proof {
                lemma_strict_sorted_contains(v@[i], w@, 0, (j as int) + 1);
            }
            i = i + 1;
            j = j + 1;
        } else if v[i] < w[j] {
            return false;
        } else {
            j = j + 1;
        }
    }
    
    i == n
}
// </vc-code>

fn main() {}

}