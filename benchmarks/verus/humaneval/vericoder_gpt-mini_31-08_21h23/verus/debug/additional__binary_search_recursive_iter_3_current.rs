use vstd::prelude::*;

verus! {

// <vc-helpers>
// No additional helpers required.
// </vc-helpers>

// <vc-spec>
fn binary_search_recursive(v: &[i32], elem: i32, c: isize, f: isize) -> (p: isize)
    // pre-conditions-start
    requires
        v.len() <= 100_000,
        forall|i: int, j: int| 0 <= i < j < v.len() ==> v[i] <= v[j],
        0 <= c <= f + 1 <= v.len(),
        forall|k: int| 0 <= k < c ==> v[k] <= elem,
        forall|k: int| f < k < v.len() ==> v[k] > elem,
    // pre-conditions-end
    // post-conditions-start
    ensures
        -1 <= p < v.len(),
        forall|u: int| 0 <= u <= p ==> v[u] <= elem,
        forall|w: int| p < w < v.len() ==> v[w] > elem,
    // post-conditions-end
    decreases f - c + 1
// </vc-spec>
// <vc-code>
{
    if c > f {
        c - 1
    } else {
        let m: isize = (c + f) / 2;
        if v[m as int] <= elem {
            proof {
                // bounds for recursive call (m+1, f): 0 <= m+1 <= f+1 <= v.len()
                assert(0 <= c); // from pre
                assert(m + 1 <= f + 1); // since m <= f
                assert(f + 1 <= v.len() as isize); // from pre

                // Prove: forall k: 0 <= k < m+1 ==> v[k] <= elem
                {
                    // Fix arbitrary k
                    let k: int = choose(|k: int| 0 <= k && k < (m + 1) as int);
                    proof {
                        if k < c as int {
                            // from precondition: forall k < c ==> v[k] <= elem
                            assert(forall|kk: int| 0 <= kk && kk < c as int ==> v[kk] <= elem);
                            assert(v[k] <= elem);
                        } else {
                            // c <= k < m+1  => k <= m
                            // from sortedness: v[k] <= v[m]
                            assert(forall|i: int, j: int| 0 <= i < j < v.len() ==> v[i] <= v[j]);
                            assert(0 <= k && k < (m as int) + 1);
                            assert(v[k] <= v[m as int]);
                            // from branch condition: v[m] <= elem
                            assert(v[m as int] <= elem);
                            assert(v[k] <= elem);
                        }
                    }
                    // Re-quantify
                    assert(forall|kk: int| 0 <= kk && kk < (m + 1) as int ==> v[kk] <= elem);
                }

                // forall k: f < k < v.len() ==> v[k] > elem remains from pre
                assert(forall|kk: int| f as int < kk && kk < v.len() as int ==> v[kk] > elem);
            }
            binary_search_recursive(v, elem, m + 1, f)
        } else {
            proof {
                // bounds for recursive call (c, m-1): 0 <= c <= m-1+1 <= v.len()
                assert(0 <= c); // from pre
                assert(c <= f + 1); // from pre
                assert(m - 1 + 1 == m);
                assert(c <= m); // since m >= c
                assert(m <= v.len() as isize); // because m <= f and f+1 <= v.len()
                // thus 0 <= c <= m-1+1 <= v.len()

                // forall k < c ==> v[k] <= elem is same as original precondition
                assert(forall|kk: int| 0 <= kk && kk < c as int ==> v[kk] <= elem);

                // Prove: forall k with m <= k < v.len() ==> v[k] > elem
                {
                    let k: int = choose(|k: int| m as int <= k && k < v.len() as int);
                    proof {
                        if k > f as int {
                            // original precondition covers k > f
                            assert(forall|kk: int| f as int < kk && kk < v.len() as int ==> v[kk] > elem);
                            assert(v[k] > elem);
                        } else {
                            // m <= k <= f: sortedness gives v[m] <= v[k], and v[m] > elem by branch
                            assert(forall|i: int, j: int| 0 <= i < j < v.len() ==> v[i] <= v[j]);
                            assert(v[m as int] > elem);
                            assert(v[m as int] <= v[k]);
                            assert(v[k] > elem);
                        }
                    }
                    assert(forall|kk: int| m as int <= kk && kk < v.len() as int ==> v[kk] > elem);
                }
            }
            binary_search_recursive(v, elem, c, m - 1)
        }
    }
}
// </vc-code>

fn main() {}
}