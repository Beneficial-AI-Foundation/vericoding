use vstd::prelude::*;

verus! {

spec fn strict_sorted(s: Seq<i32>) -> bool {
    forall|u: int, w: int| 0 <= u < w < s.len() ==> s[u] < s[w]
}

// <vc-helpers>
proof fn lemma_strict_sorted_implies_no_duplicates(s: Seq<i32>)
    requires strict_sorted(s)
    ensures forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] != s[j]
{
    assert forall|i: int, j: int| 0 <= i < j < s.len() implies s[i] != s[j] by {
        if 0 <= i < j < s.len() {
            assert(s[i] < s[j]);
        }
    }
}

proof fn lemma_strict_sorted_transitive(s: Seq<i32>, i: int, j: int, k: int)
    requires strict_sorted(s), 0 <= i < j < k < s.len()
    ensures s[i] < s[j] < s[k]
{
}

proof fn lemma_subrange_contains_transitivity(w: Seq<i32>, m: int, j: int, elem: i32)
    requires 0 <= j < m <= w.len(), w[j] == elem
    ensures w.subrange(0, m).contains(elem)
{
    assert(w.subrange(0, m)[j] == elem);
}

proof fn lemma_strict_sorted_prefix(s: Seq<i32>, i: int, j: int)
    requires strict_sorted(s), 0 <= i < s.len(), 0 <= j < s.len(), i < j
    ensures s[i] < s[j]
{
}

proof fn lemma_no_element_in_subrange(w: Seq<i32>, m: int, elem: i32)
    requires 
        strict_sorted(w),
        0 < m <= w.len(),
        forall|k: int| 0 <= k < m ==> w[k] < elem
    ensures !w.subrange(0, m).contains(elem)
{
    assert forall|k: int| 0 <= k < m implies w.subrange(0, m)[k] != elem by {
        if 0 <= k < m {
            assert(w[k] < elem);
            assert(w.subrange(0, m)[k] == w[k]);
        }
    }
}

proof fn lemma_all_elements_less_than(w: Seq<i32>, j: int, elem: i32)
    requires 
        strict_sorted(w),
        0 <= j < w.len(),
        w[j] > elem
    ensures forall|k: int| 0 <= k <= j ==> w[k] < elem || w[k] > elem
{
    assert forall|k: int| 0 <= k <= j implies w[k] < elem || w[k] > elem by {
        if 0 <= k <= j {
            if k == j {
                assert(w[k] > elem);
            } else if k < j {
                assert(w[k] < w[j]);
                assert(w[j] > elem);
            }
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
    if n == 0 {
        return true;
    }
    
    let mut i: usize = 0;
    let mut j: usize = 0;
    
    while i < n && j < m
        invariant
            0 <= i <= n,
            0 <= j <= m,
            n <= v@.len(),
            m <= w@.len(),
            forall|k: int| 0 <= k < i ==> w@.subrange(0, m as int).contains(v@[k]),
            i < n ==> (forall|k: int| 0 <= k < j ==> w@[k] < v@[i as int]),
        decreases (n - i) + (m - j)
    {
        if v[i] == w[j] {
            proof {
                lemma_subrange_contains_transitivity(w@, m as int, j as int, v@[i as int]);
            }
            i = i + 1;
            j = j + 1;
        } else if v[i] < w[j] {
            proof {
                assert(forall|k: int| 0 <= k < j ==> w@[k] < v@[i as int]);
                assert(w@[j as int] > v@[i as int]);
                assert forall|k: int| 0 <= k <= j implies w@[k] < v@[i as int] || w@[k] > v@[i as int] by {
                    if 0 <= k <= j {
                        if k == j {
                            assert(w@[k] > v@[i as int]);
                        } else {
                            assert(w@[k] < v@[i as int]);
                        }
                    }
                }
                assert forall|k: int| 0 <= k < m implies w@[k] < v@[i as int] || w@[k] >= v@[i as int] by {
                    if 0 <= k < m {
                        if k <= j {
                            assert(w@[k] < v@[i as int] || w@[k] > v@[i as int]);
                        } else {
                            assert(w@[j as int] < w@[k]);
                            assert(w@[j as int] > v@[i as int]);
                        }
                    }
                }
                lemma_no_element_in_subrange(w@, m as int, v@[i as int]);
            }
            return false;
        } else {
            j = j + 1;
        }
    }
    
    if i == n {
        proof {
            assert(forall|k: int| 0 <= k < n ==> w@.subrange(0, m as int).contains(v@[k]));
        }
        true
    } else {
        proof {
            assert(j == m);
            assert(i < n);
            assert(forall|k: int| 0 <= k < j ==> w@[k] < v@[i as int]);
            assert(j == m);
            assert forall|k: int| 0 <= k < m implies w@[k] < v@[i as int] by {
                if 0 <= k < m {
                    assert(k < j);
                    assert(w@[k] < v@[i as int]);
                }
            }
            lemma_no_element_in_subrange(w@, m as int, v@[i as int]);
        }
        false
    }
}
// </vc-code>

fn main() {}

}