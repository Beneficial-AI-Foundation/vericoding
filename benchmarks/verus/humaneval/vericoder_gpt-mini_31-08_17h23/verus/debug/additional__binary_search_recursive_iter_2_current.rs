use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn mid_bounds(c: isize, f: isize)
    requires
        c <= f,
    ensures
        c <= (c + f) / 2,
        (c + f) / 2 <= f
{
    // 2*c <= c+f <= 2*f
    assert(2 * c <= c + f);
    assert(c + f <= 2 * f);
    // dividing by 2 preserves inequalities for integers
    assert(c <= (c + f) / 2);
    assert((c + f) / 2 <= f);
}

proof fn sorted_implies_le(v: &[i32], i: isize, j: isize)
    requires
        0 <= i <= j < v.len(),
        forall|a: isize, b: isize| 0 <= a < b < v.len() ==> v[a as usize] <= v[b as usize],
    ensures
        v[i as usize] <= v[j as usize],
{
    if i < j {
        // instantiate the quantified sorted property with a=i, b=j
        assert(v[i as usize] <= v[j as usize]);
    } else {
        // i == j
        assert(v[i as usize] == v[j as usize]);
        assert(v[i as usize] <= v[j as usize]);
    }
}
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
fn binary_search_recursive(v: &[i32], elem: i32, c: isize, f: isize) -> (p: isize)
    // pre-conditions-start
    requires
        v.len() <= 100_000,
        forall|i: int, j: int| 0 <= i < j < v.len() ==> v[i as usize] <= v[j as usize],
        0 <= c <= f + 1 <= v.len(),
        forall|k: int| 0 <= k < c ==> v[k as usize] <= elem,
        forall|k: int| f < k < v.len() ==> v[k as usize] > elem,
    // pre-conditions-end
    // post-conditions-start
    ensures
        -1 <= p < v.len(),
        forall|u: int| 0 <= u <= p ==> v[u as usize] <= elem,
        forall|w: int| p < w < v.len() ==> v[w as usize] > elem,
    // post-conditions-end
    decreases f - c + 1
{
    if c > f {
        // empty interval: return c-1
        let res: isize = c - 1;
        // prove postconditions for res
        // bounds: -1 <= res < v.len()
        assert(-1 <= res);
        // res < v.len(): res = c-1 and c <= f+1 <= v.len() ==> c-1 < v.len()
        assert(res < v.len());
        // forall u with 0 <= u <= res => u < c hence v[u] <= elem by precondition
        proof {
            assert(forall|u: int| 0 <= u <= res ==> v[u as usize] <= elem);
        }
        // forall w with res < w < v.len() => w >= c hence w > f (since c > f) so precondition gives v[w] > elem
        proof {
            assert(forall|w: int| res < w < v.len() ==> v[w as usize] > elem);
        }
        return res;
    } else {
        // c <= f, non-empty interval
        let m: isize = (c + f) / 2;
        // bounds for m: c <= m <= f
        proof {
            mid_bounds(c, f);
        }
        if v[m as usize] <= elem {
            // we will search in [m+1 .. f]
            let newc: isize = m + 1;
            // prove recursive preconditions for (newc, f)
            proof {
                // 0 <= newc
                assert(0 <= newc);
                // newc <= f + 1 because m <= f
                assert(newc <= f + 1);
                // f + 1 <= v.len() holds from original pre
                assert(f + 1 <= v.len());
                // forall k < newc => v[k] <= elem
                assert(forall|k: int| 0 <= k < newc ==> v[k as usize] <= elem);
                // proof of the above quantified assertion
                {
                    // take arbitrary k satisfying 0 <= k < newc
                    reveal(forall|k: int| 0 <= k < newc ==> v[k as usize] <= elem);
                    // manual proof:
                    // if k < c then precondition gives v[k] <= elem
                    // else c <= k <= m and sortedness gives v[k] <= v[m] and v[m] <= elem
                    // The proof is done by cases using existing preconditions and sorted_implies_le
                    assert(forall|k: int| 0 <= k < newc ==>
                        (if k < c {
                            // k < c
                            v[k as usize] <= elem
                        } else {
                            // c <= k < m+1 => c <= k <= m
                            {
                                // 0 <= k <= m < v.len()
                                assert(0 <= k && k <= m && m < v.len());
                                sorted_implies_le(v, k, m);
                                assert(v[k as usize] <= v[m as usize]);
                                assert(v[m as usize] <= elem);
                                v[k as usize] <= elem
                            }
                        })
                    );
                }
                // forall k > f => v[k] > elem preserved from original pre
                assert(forall|k: int| f < k < v.len() ==> v[k as usize] > elem);
            }
            let res = binary_search_recursive(v, elem, newc, f);
            return res;
        } else {
            // v[m] > elem, search in [c .. m-1]
            let newf: isize = m - 1;
            // prove recursive preconditions for (c, newf)
            proof {
                // 0 <= c holds
                assert(0 <= c);
                // c <= newf + 1 because newf + 1 = m and c <= m
                assert(c <= newf + 1);
                // newf + 1 <= v.len(): m <= v.len()
                assert(newf + 1 <= v.len());
                // forall k < c => v[k] <= elem preserved from original pre
                assert(forall|k: int| 0 <= k < c ==> v[k as usize] <= elem);
                // forall k > newf => v[k] > elem
                // if k > newf then k >= m. For k >= m and k <= f, v[k] >= v[m] > elem by sortedness.
                // For k > f original pre gives > elem as well.
                assert(forall|k: int| newf < k < v.len() ==> v[k as usize] > elem);
                {
                    // detailed proof: take k with newf < k < v.len()
                    // then k >= m. If k > f, original pre applies. Else m <= k <= f and sorted_implies_le gives v[m] <= v[k], so v[k] > elem.
                    reveal(forall|k: int| newf < k < v.len() ==> v[k as usize] > elem);
                    assert(forall|k: int| newf < k < v.len() ==>
                        (if f < k {
                            v[k as usize] > elem
                        } else {
                            // m <= k <= f
                            {
                                // 0 <= m <= k <= f < v.len()
                                assert(0 <= m && m <= k && k < v.len());
                                sorted_implies_le(v, m, k);
                                assert(v[m as usize] <= v[k as usize]);
                                assert(v[m as usize] > elem);
                                v[k as usize] > elem
                            }
                        })
                    );
                }
            }
            let res = binary_search_recursive(v, elem, c, newf);
            return res;
        }
    }
}
// </vc-code>

fn main() {}
}