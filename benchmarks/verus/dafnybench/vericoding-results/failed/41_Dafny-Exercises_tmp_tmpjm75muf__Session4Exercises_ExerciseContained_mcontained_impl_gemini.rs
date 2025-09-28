// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn strict_sorted(s: Seq<i32>) -> bool {
    forall|u: int, w: int| 0 <= u < w < s.len() ==> s[u] < s[w]
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn mcontained(v: &[i32], w: &[i32], n: usize, m: usize) -> (b: bool)
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
    /* code modified by LLM (iteration 4): fixed compilation errors by casting usize indices to int for spec access */
    let mut i: usize = 0;
    let mut j: usize = 0;

    while i < n && j < m
        invariant
            0 <= i <= n,
            0 <= j <= m,
            // All v elements processed so far are contained in the w prefix. 
            forall|k: int| 0 <= k < i ==> w@.subrange(0, j as int).contains(v@[k as int]),
            // The next element of v to find is greater than the w prefix scanned so far.
            i < n ==> (forall|l: int| 0 <= l < j ==> w@[l] < v@[i as int]),
        decreases n - i, m - j
    {
        if v[i] > w[j] {
            j = j + 1;
        } else if v[i] < w[j] {
            proof {
                assert forall|l: int| 0 <= l < m implies w@[l] != v@[i as int] by {
                    if l < j {
                        assert(w@[l] < v@[i as int]);
                    } else if l == j {
                        assert(w@[l] > v@[i as int]);
                    } else { // l > j
                        assert(strict_sorted(w@));
                        assert(v@[i as int] < w@[j as int]);
                        assert(w@[j as int] < w@[l]);
                    }
                };
                assert(!w.view().subrange(0, m as int).contains(v@[i as int]));
            }
            return false;
        } else { // v[i] == w[j]
            proof {
                if i + 1 < n {
                    assert forall|l: int| 0 <= l < j + 1 implies w@[l] < v@[(i + 1) as int] by {
                        assert(strict_sorted(w@));
                        assert(strict_sorted(v@));
                        assert(l <= j ==> w@[l] <= w@[j as int]);
                        assert(w@[j as int] == v@[i as int]);
                        assert(v@[i as int] < v@[(i + 1) as int]);
                    };
                }
            }
            i = i + 1;
            j = j + 1;
        }
    }

    if i == n {
        true
    } else { // i < n && j == m
        proof {
            assert(i < n && j == m);
            assert(forall|l: int| 0 <= l < m ==> w@[l] < v@[i as int]);
            assert forall|l: int| 0 <= l < m implies w@[l] != v@[i as int] by {
                assert(w@[l] < v@[i as int]);
            };
            assert(!w.view().subrange(0, m as int).contains(v@[i as int]));
        }
        false
    }
}
// </vc-code>

}
fn main() {}