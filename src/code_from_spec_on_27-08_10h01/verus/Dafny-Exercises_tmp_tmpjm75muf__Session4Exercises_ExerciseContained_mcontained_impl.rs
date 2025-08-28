use vstd::prelude::*;

verus! {

spec fn strict_sorted(s: Seq<i32>) -> bool {
    forall|u: int, w: int| 0 <= u < w < s.len() ==> s[u] < s[w]
}

// <vc-helpers>
proof fn lemma_strict_sorted_implies_no_duplicates(s: Seq<i32>, i: int, j: int)
    requires
        strict_sorted(s),
        0 <= i < s.len(),
        0 <= j < s.len(),
        i != j
    ensures
        s[i] != s[j]
{
    if i < j {
        assert(s[i] < s[j]);
    } else {
        assert(s[j] < s[i]);
    }
}

proof fn lemma_strict_sorted_subrange(s: Seq<i32>, start: int, end: int)
    requires
        strict_sorted(s),
        0 <= start <= end <= s.len()
    ensures
        strict_sorted(s.subrange(start, end))
{
    let sub = s.subrange(start, end);
    assert forall|u: int, w: int| 0 <= u < w < sub.len() implies sub[u] < sub[w] by {
        assert(sub[u] == s[start + u]);
        assert(sub[w] == s[start + w]);
        assert(start + u < start + w);
        assert(s[start + u] < s[start + w]);
    }
}

proof fn lemma_contains_subrange(s: Seq<i32>, x: i32, m: int)
    requires
        0 <= m <= s.len(),
        s.subrange(0, m).contains(x)
    ensures
        s.contains(x)
{
}
// </vc-helpers>

// <vc-spec>
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
// </vc-spec>

// <vc-code>
{
    let mut i: usize = 0;
    let mut j: usize = 0;
    
    while i < n && j < m
        invariant
            i <= n,
            j <= m,
            n <= v@.len(),
            m <= w@.len(),
            forall|k: int| 0 <= k < i ==> w@.subrange(0, m as int).contains(v@[k])
        decreases (n - i) + (m - j)
    {
        if v[i] == w[j] {
            i += 1;
            j += 1;
        } else if v[i] < w[j] {
            return false;
        } else {
            j += 1;
        }
    }
    
    if i == n {
        true
    } else {
        false
    }
}
// </vc-code>

fn main() {}

}