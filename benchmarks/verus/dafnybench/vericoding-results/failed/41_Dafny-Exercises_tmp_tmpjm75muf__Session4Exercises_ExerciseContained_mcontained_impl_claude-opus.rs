use vstd::prelude::*;

verus! {

spec fn strict_sorted(s: Seq<i32>) -> bool {
    forall|u: int, w: int| 0 <= u < w < s.len() ==> s[u] < s[w]
}

// <vc-helpers>
proof fn strict_sorted_implies_unique(s: Seq<i32>, i: int, j: int)
    requires
        strict_sorted(s),
        0 <= i < s.len(),
        0 <= j < s.len(),
        i != j,
    ensures
        s[i] != s[j]
{
    if i < j {
        assert(s[i] < s[j]);
    } else {
        assert(s[j] < s[i]);
    }
}

proof fn strict_sorted_subrange(s: Seq<i32>, start: int, end: int)
    requires
        strict_sorted(s),
        0 <= start <= end <= s.len(),
    ensures
        strict_sorted(s.subrange(start, end))
{
    assert forall|u: int, w: int| 0 <= u < w < s.subrange(start, end).len() implies
        s.subrange(start, end)[u] < s.subrange(start, end)[w] by {
        assert(s.subrange(start, end)[u] == s[start + u]);
        assert(s.subrange(start, end)[w] == s[start + w]);
        assert(s[start + u] < s[start + w]);
    }
}

proof fn element_not_in_smaller_prefix(w: Seq<i32>, j: int, m: int, target: i32)
    requires
        strict_sorted(w),
        0 <= j < m <= w.len(),
        w[j] > target,
    ensures
        !w.subrange(0, j).contains(target)
{
    if w.subrange(0, j).contains(target) {
        let idx = choose|idx: int| 0 <= idx < j && w[idx] == target;
        assert(w[idx] == target);
        assert(w[idx] < w[j]);
        assert(target < w[j]);
        assert(w[j] > target && target < w[j]);
        // This is a contradiction
    }
}

proof fn element_not_in_larger_suffix(w: Seq<i32>, j: int, m: int, target: i32)
    requires
        strict_sorted(w),
        0 <= j < m <= w.len(),
        w[j] > target,
    ensures
        !w.subrange(j, m).contains(target)
{
    assert forall|idx: int| j <= idx < m implies w[idx] != target by {
        if j == idx {
            assert(w[idx] > target);
        } else {
            assert(j < idx);
            assert(w[j] < w[idx]);
            assert(target < w[j]);
            assert(target < w[idx]);
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
    
    while i < n
        invariant
            i <= n,
            j <= m,
            i <= j,
            strict_sorted(v@),
            strict_sorted(w@),
            v@.len() >= n,
            w@.len() >= m,
            n <= m,
            forall|k: int| #![auto] 0 <= k < i ==> w@.subrange(0, m as int).contains(v@[k]),
            forall|k: int| #![auto] 0 <= k < i ==> w@.subrange(0, j as int).contains(v@[k]),
            j < m ==> forall|k: int| #![auto] i as int <= k < n ==> v@[k] > w@[j as int],
        decreases n - i
    {
        if j >= m {
            // We've exhausted w but still have elements in v to check
            return false;
        }
        
        if v[i] == w[j] {
            proof {
                assert(w@[j as int] == v@[i as int]);
                assert(w@.subrange(0, m as int).contains(v@[i as int]));
                assert forall|k: int| #![auto] 0 <= k < i + 1 implies w@.subrange(0, m as int).contains(v@[k]) by {
                    if k < i as int {
                        assert(w@.subrange(0, m as int).contains(v@[k]));
                    } else {
                        assert(k == i as int);
                        assert(w@.subrange(0, m as int).contains(v@[i as int]));
                    }
                }
                assert forall|k: int| #![auto] 0 <= k < i + 1 implies w@.subrange(0, (j + 1) as int).contains(v@[k]) by {
                    if k < i as int {
                        assert(w@.subrange(0, j as int).contains(v@[k]));
                        assert(w@.subrange(0, (j + 1) as int).contains(v@[k]));
                    } else {
                        assert(k == i as int);
                        assert(v@[k] == w@[j as int]);
                        assert(w@.subrange(0, (j + 1) as int).contains(v@[k]));
                    }
                }
                if j + 1 < m {
                    assert forall|k: int| #![auto] (i + 1) as int <= k < n implies v@[k] > w@[(j + 1) as int] by {
                        assert(v@[k] > v@[i as int]);
                        assert(v@[i as int] == w@[j as int]);
                        assert(w@[j as int] < w@[(j + 1) as int]);
                        assert(v@[k] > w@[(j + 1) as int]);
                    }
                }
            }
            i = i + 1;
            j = j + 1;
        } else if v[i] < w[j] {
            proof {
                element_not_in_smaller_prefix(w@, j as int, m as int, v@[i as int]);
                assert(!w@.subrange(0
// </vc-code>

fn main() {}

}