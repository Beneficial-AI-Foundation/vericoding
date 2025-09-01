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

proof fn le_res_implies_lt_c(c: isize, res: isize)
    requires
        res == c - 1,
    ensures
        forall|u: isize| 0 <= u <= res ==> u < c
{
    assert(forall|u: isize| 0 <= u <= res ==> u < c);
}

proof fn res_lt_implies_ge_c(c: isize, res: isize)
    requires
        res == c - 1,
    ensures
        forall|w: isize| res < w ==> c <= w
{
    assert(forall|w: isize| res < w ==> c <= w);
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
        forall|i: isize, j: isize| 0 <= i < j < v.len() ==> v[i as usize] <= v[j as usize],
        0 <= c <= f + 1 <= v.len(),
        forall|k: isize| 0 <= k < c ==> v[k as usize] <= elem,
        forall|k: isize| f < k < v.len() ==> v[k as usize] > elem,
    // pre-conditions-end
    // post-conditions-start
    ensures
        -1 <= p < v.len(),
        forall|u: isize| 0 <= u <= p ==> v[u as usize] <= elem,
        forall|w: isize| p < w < v.len() ==> v[w as usize] > elem,
    // post-conditions-end
    decreases f - c + 1
{
    if c > f {
        // empty interval: return c-1
        let res: isize = c - 1;
        // bounds: -1 <= res
        assert(-1 <= res);
        // res < v.len(): res = c-1 and c <= f+1 <= v.len() ==> c-1 < v.len()
        assert(res < v.len());

        // forall u with 0 <= u <= res => u < c, then use precondition to get v[u] <= elem
        proof {
            le_res_implies_lt_c(c, res);
        }
        assert(forall|u: isize| 0 <= u <= res ==> v[u as usize] <= elem);

        // forall w with res < w < v.len() => w >= c and since c > f, w > f => precondition gives v[w] > elem
        proof {
            res_lt_implies_ge_c(c, res);
        }
        assert(forall|w: isize| res < w < v.len() ==> v[w as usize] > elem);

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
                // measure decreases: f - newc + 1 < f - c + 1
                assert(f - newc + 1 < f - c + 1);
            }

            // Prove the quantified preconditions required by the recursive call.
            // For indices k with 0 <= k < newc, we need v[k] <= elem.
            // Split into k < c (handled by original pre) and c <= k <= m (handled by sorted property and v[m] <= elem).
            proof {
                assert(forall|k: isize| 0 <= k < newc ==>
                    (k < c || (c <= k && k <= m))
                );
                // Now establish the desired relation
                assert(forall|k: isize| 0 <= k < newc ==>
                    (if k < c {
                        v[k as usize] <= elem
                    } else {
                        // c <= k <= m
                        // From sorted property we have v[k] <= v[m], and v[m] <= elem by the branch condition
                        sorted_implies_le(v, k, m);
                        assert(v[k as usize] <= v[m as usize]);
                        assert(v[m as usize] <= elem);
                        v[k as usize] <= elem
                    })
                );
            }

            // The tail condition f < k preserved from original pre
            assert(forall|k: isize| f < k < v.len() ==> v[k as usize] > elem);

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
                // measure decreases: newf - c + 1 < f - c + 1
                assert(newf - c + 1 < f - c + 1);
            }

            // Prove the quantified preconditions required by the recursive call.
            // For indices k with newf < k < v.len(), we need v[k] > elem.
            // Split into k > f (handled by original pre) and m <= k <= f (handled by sorted property and v[m] > elem).
            proof {
                assert(forall|k: isize| newf < k < v.len() ==>
                    (if f < k {
                        v[k as usize] > elem
                    } else {
                        // m <= k <= f
                        sorted_implies_le(v, m, k);
                        assert(v[m as usize] <= v[k as usize]);
                        // we know v[m] > elem
                        assert(v[m as usize] > elem);
                        v[k as usize] > elem
                    })
                );
            }

            // The head condition 0 <= k < c preserved from original pre
            assert(forall|k: isize| 0 <= k < c ==> v[k as usize] <= elem);

            let res = binary_search_recursive(v, elem, c, newf);
            return res;
        }
    }
}
// </vc-code>

fn main() {}
}