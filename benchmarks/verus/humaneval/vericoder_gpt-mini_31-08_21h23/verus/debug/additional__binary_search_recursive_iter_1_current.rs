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
    // impl-start
    if c > f {
        c - 1
    } else {
        let m: isize = (c + f) / 2;
        let m_usize: usize = (m as usize);
        if v[m_usize] <= elem {
            // prove preconditions for recursive call with (m+1, f)
            proof {
                // bounds: 0 <= m+1 <= f+1 <= v.len()
                assert(0 <= c); // from pre
                assert(c <= m + 1); // m >= c implies m+1 >= c+1, but we only need non-negativity
                assert(m + 1 <= f + 1); // since m <= f
                assert(f + 1 <= v.len() as isize); // from pre

                // forall k < m+1 ==> v[k] <= elem
                // we prove by cases: k < c or c <= k <= m
                {
                    // introduce the universal property
                    // proof by fixing arbitrary k
                    let rec_proof = |k: int| {
                        requires(0 <= k && k < (m + 1) as int);
                        ensures(v[k as usize] <= elem);
                        proof {
                            if k < c as int {
                                // from precondition: forall k < c ==> v[k] <= elem
                                assert(v[k as usize] <= elem);
                            } else {
                                // c <= k <= m
                                // from sortedness: v[k] <= v[m]
                                assert(forall|i: int, j: int| 0 <= i < j < v.len() ==> v[i] <= v[j]);
                                // instantiate sortedness with i = k, j = m
                                assert(0 <= k && k < (m as int) + 1); // ensures k <= m
                                assert(v[k as usize] <= v[m_usize]);
                                // and v[m] <= elem by branch condition
                                assert(v[m_usize] <= elem);
                                assert(v[k as usize] <= elem);
                            }
                        }
                    };
                    // instantiate the universal to satisfy the recursive call requirement
                    assert(forall|k: int| 0 <= k < (m + 1) as int ==> v[k as usize] <= elem);
                }

                // forall k > f ==> v[k] > elem is same as original precondition (unchanged)
                assert(forall|k: int| f < k < v.len() ==> v[k as usize] > elem);
            }
            binary_search_recursive(v, elem, m + 1, f)
        } else {
            // v[m] > elem: prove preconditions for recursive call with (c, m-1)
            proof {
                // bounds: 0 <= c <= (m-1) + 1 <= v.len()
                assert(0 <= c); // from pre
                assert(c <= f + 1); // from pre
                assert(m - 1 + 1 == m);
                assert(c <= m); // since m >= c
                assert(m <= v.len() as isize); // because m <= f and f+1 <= v.len()
                // thus 0 <= c <= m-1+1 <= v.len()

                // forall k < c ==> v[k] <= elem is same as original precondition
                assert(forall|k: int| 0 <= k < c as int ==> v[k as usize] <= elem);

                // forall k > m-1 ==> v[k] > elem, i.e., forall k >= m ==> v[k] > elem
                {
                    // prove for arbitrary k with m <= k < v.len()
                    let rec_proof2 = |k: int| {
                        requires(m as int <= k && k < v.len() as int);
                        ensures(v[k as usize] > elem);
                        proof {
                            // two cases: k > f or k <= f
                            if k > f as int {
                                // original precondition covers k > f
                                assert(v[k as usize] > elem);
                            } else {
                                // m <= k <= f: use sortedness and v[m] > elem
                                assert(forall|i: int, j: int| 0 <= i < j < v.len() ==> v[i] <= v[j]);
                                // from sortedness with i = m, j = k we have v[m] <= v[k]
                                // since v[m] > elem, v[k] > elem
                                assert(v[m_usize] > elem);
                                assert(v[m_usize] <= v[k as usize]);
                                assert(v[k as usize] > elem);
                            }
                        }
                    };
                    assert(forall|k: int| m as int <= k < v.len() as int ==> v[k as usize] > elem);
                }
            }
            binary_search_recursive(v, elem, c, m - 1)
        }
    }
    // impl-end
}
// </vc-code>

fn main() {}
}