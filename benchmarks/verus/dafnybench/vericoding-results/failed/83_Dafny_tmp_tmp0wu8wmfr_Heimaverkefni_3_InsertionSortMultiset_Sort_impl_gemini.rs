// <vc-preamble>
use vstd::prelude::*;
use vstd::multiset::*;

verus! {

proof fn search(s: Seq<i32>, x: i32) -> (k: usize)

    requires 
        forall|p: int, q: int| 0 <= p < q < s.len() ==> s[p] <= s[q],
    ensures 
        0 <= k <= s.len()
        && forall|i: int| 0 <= i < k ==> s[i] <= x
        && forall|i: int| k <= i < s.len() ==> s[i] >= x
        && forall|z: i32| s.subrange(0, k as int).contains(z) ==> z <= x
        && forall|z: i32| s.subrange(k as int, s.len() as int).contains(z) ==> z >= x
        && s == s.subrange(0, k as int) + s.subrange(k as int, s.len() as int),
{
  assume(false);
  0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed compilation errors by using correct types and indexing */
fn find_insertion_point(s: Seq<i32>, x: i32) -> (k: usize)
    requires
        forall|p: int, q: int| 0 <= p < q < s.len() ==> s[p] <= s[q],
    ensures
        0 <= k <= s.len(),
        forall|i: int| 0 <= i < (k as int) ==> s[i] <= x,
        forall|i: int| (k as int) <= i < s.len() ==> s[i] >= x,
{
    let mut low: usize = 0;
    let mut high: usize = s.len() as usize;
    while low < high
        invariant
            0 <= low <= high <= s.len(),
            forall|i: int| 0 <= i < (low as int) ==> s[i] <= x,
            forall|i: int| (high as int) <= i < s.len() ==> s[i] >= x,
        decreases high - low,
    {
        let mid = low + (high - low) / 2;
        if s.index(mid) < x {
            low = mid + 1;
        } else {
            high = mid;
        }
    }
    low
}

/* helper modified by LLM (iteration 5): fixed compilation errors with types and indexing */
proof fn lemma_insert_sorted(s: Seq<i32>, x: i32, k: int)
    requires
        0 <= k <= s.len(),
        forall|p: int, q: int| 0 <= p < q < s.len() ==> s[p] <= s[q],
        forall|i: int| 0 <= i < k ==> s[i] <= x,
        forall|i: int| k <= i < s.len() ==> s[i] >= x,
    ensures
        forall|p: int, q: int|
            0 <= p < q < s.insert(k, x).len() ==> s.insert(k, x)[p] <= s.insert(k, x)[q],
{
}
// </vc-helpers>

// <vc-spec>
fn sort(m: Multiset<i32>) -> (r: Seq<i32>)
    ensures 
        r.to_multiset() == m
        && forall|p: int, q: int| 0 <= p < q < r.len() ==> r[p] <= r[q],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed compilation errors with types and multiset logic */
    let mut r: Seq<i32> = Seq::empty();
    let mut m_mut = m;
    while !m_mut.is_empty()
        invariant
            m == m_mut + r.to_multiset(),
            forall|p: int, q: int| 0 <= p < q < r.len() ==> r[p] <= r[q],
        decreases m_mut.len()
    {
        let x = m_mut.choose();

        let k = find_insertion_point(r, x);
        
        proof {
            lemma_insert_sorted(r, x, k as int);
            vstd::seq_lib::to_multiset_insert(r, k as int, x);
        }

        m_mut = m_mut.remove(x);
        r = r.insert(k as int, x);
    }
    r
}
// </vc-code>

}
fn main() {}