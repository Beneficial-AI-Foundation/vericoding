use vstd::prelude::*;

verus! {

spec fn sorted(s: Seq<i32>) -> bool {
    forall|u: int, w: int| 0 <= u < w < s.len() ==> s[u] <= s[w]
}







//Recursive binary search

// <vc-helpers>
fn midpoint(low: usize, high: usize) -> usize
    requires
        low <= high,
    ensures
        low <= result <= high,
{
    low + (high - low) / 2
}
// </vc-helpers>

// <vc-spec>
fn binary_search_rec(v: &Vec<i32>, elem: i32, c: usize, f: usize) -> (p: i32)
    requires
        sorted(v@),
        0 <= c <= f + 1 <= v.len(),//0<=c<=v.Length && -1<=f<v.Length && c<=f+1
        forall|k: int| 0 <= k < c ==> v[k] <= elem,
        forall|k: int| f < k < v.len() ==> v[k] > elem,
    ensures
        -1 <= p < v.len(),
        (forall|u: int| 0 <= u <= p ==> v[u] <= elem) && (forall|w: int| p < w < v.len() ==> v[w] > elem),
    decreases f - c
// </vc-spec>
// <vc-code>
{
    let v_seq = v@;
    if c > f {
        // Base case: The search range is empty.
        // All elements to the left of 'c' (or 'f+1') are <= elem, and all elements to the right are > elem.
        // Therefore, 'f' is the correct insertion point (-1 if f is usize_max, implying not found)
        proof {
            assert forall |u: int| 0 <= u <= f implies v_seq[u] <= elem by {
                if 0 <= u && (u as usize) < c {
                    assert(v_seq[u] <= elem);
                } else if (u as usize) == c && c == f+1 {
                    // This case means the range c..f is empty because c = f+1.
                    // If 0 <= u <= f, then u is not in [c,f] or [c, mid-1], etc.
                    // If c = f+1, then f is the insertion point.
                    // This loop condition (0 <= u <= f) covers the elements that are less than or equal to `elem`.
                    // If this path is reached, it implies `u` is outside the range `[0, c)`.
                    // But if `u <= f` and `c = f+1`, then `u < c`. So this must follow `0 <= u < c`.
                }
            }
        }
        f as i32
    } else {
        let mid = midpoint(c, f);
        if v_seq[mid] <= elem {
            // elem could be at mid or to its right.
            // All elements to the left of mid (from c to mid-1) are already known to be <= elem.
            // We additionally know that v_seq[mid] <= elem.
            // So, for the next recursive call, new_c is mid + 1.
            // The elements from c to mid are <= elem.
            // The elements from f+1 to end are > elem.
            // New call: binary_search_rec(v, elem, mid + 1, f)
            proof {
                assert(mid + 1 <= f + 1); // For the new c and f. mid <= f, so mid+1 <= f+1.
                // We need to prove the preconditions for the recursive call:
                // 1. sorted(v@) -- unchanged, holds
                // 2. 0 <= new_c <= new_f + 1 <= v.len()
                //    0 <= mid + 1: true since mid >= 0 (midpoint returns usize)
                //    mid + 1 <= f + 1: true since mid <= f
                //    f + 1 <= v.len(): true by original precondition
                // 3. forall|k: int| 0 <= k < new_c ==> v[k] <= elem
                //    forall|k: int| 0 <= k < mid + 1 ==> v[k] <= elem
                //    If 0 <= k < c, then v[k] <= elem (by original precon).
                //    If c <= k <= mid, then v[k] <= v[mid] (since sorted(v@)).
                //    We know v[mid] <= elem. So v[k] <= elem.
                //    Thus, forall|k: int| 0 <= k <= mid ==> v[k] <= elem.
                //    This implies forall|k: int| 0 <= k < mid + 1 ==> v[k] <= elem.
                assert forall |k: int| 0 <= k < (mid + 1) as int implies v_seq[k] <= elem by {
                    if (k as usize) < c {
                        assert(v_seq[k] <= elem); // From original precondition
                    } else if (k as usize) <= mid {
                        assert(v_seq[k] <= v_seq[mid]); // From sorted(v_seq)
                        assert(v_seq[mid] <= elem); // From current if branch
                        assert(v_seq[k] <= elem);
                    }
                }
                // 4. forall|k: int| new_f < k < v.len() ==> v[k] > elem
                //    forall|k: int| f < k < v.len() ==> v[k] > elem
                //    This is precisely the original precondition for 'f', so it holds.
            }
            binary_search_rec(v, elem, mid + 1, f)
        } else {
            // elem must be to the left of mid.
            // All elements from mid to f are > elem or unknown.
            // Since v_seq[mid] > elem, we know that elements from mid to f are not valid candidates.
            // New elements that are now known to be > elem are from mid to end.
            // The elements from c to f are candidates.
            // The elements from mid (new_f) to end are > elem.
            // Original `forall|k: int| f < k < v.len() ==> v[k] > elem` is maintained.
            // Mid becomes the new 'f' (midpoint - 1 effectively).
            // New call: binary_search_rec(v, elem, c, mid - 1)
            proof {
                assert((mid as int) >= 0); // mid is usize, so mid >= 0 holds
                // We need to prove the preconditions for the recursive call:
                // 1. sorted(v@) -- unchanged, holds
                // 2. 0 <= new_c <= new_f + 1 <= v.len()
                //    0 <= c: true by original precondition
                //    c <= mid -1 + 1: c <= mid, true since mid is midpoint(c,f) and mid >= c
                //    mid - 1 + 1 <= v.len(): mid <= v.len(). True since mid <= f < v.len()
                assert(c <= mid); // mid = c + (f-c)/2, so mid >= c
                // 3. forall|k: int| 0 <= k < new_c ==> v[k] <= elem
                //    forall|k: int| 0 <= k < c ==> v[k] <= elem
                //    This is precisely the original precondition for 'c', so it holds.
                // 4. forall|k: int| new_f < k < v.len() ==> v[k] > elem
                //    forall|k: int| (mid - 1) < k < v.len() ==> v[k] > elem.
                //    This means forall|k: int| mid <= k < v.len() ==> v[k] > elem.
                //    We know v_seq[mid] > elem from the current if/else branch.
                //    Since v_seq is sorted, for any k > mid, v_seq[k] >= v_seq[mid].
                //    Therefore, v_seq[k] > elem.
                //    If k > f, then we know from original precondition v[k] > elem.
                //    So we need to cover the range mid <= k <= f.
                assert forall |k: int| (mid as int) <= k < v_seq.len() implies v_seq[k] > elem by {
                    assert(sorted(v_seq));
                    if k == mid as int {
                        assert(v_seq[mid] > elem); // From current else branch
                    } else if (k as usize) > mid && (k as usize) <= f {
                        assert(v_seq[k] >= v_seq[mid]); // From sorted(v_seq)
                        assert(v_seq[mid] > elem); // From current else branch
                        assert(v_seq[k] > elem);
                    } else if (k as usize) > f {
                        assert(v_seq[k] > elem); // From original precondition
                    }
                }
            }
            binary_search_rec(v, elem, c, mid - 1)
        }
    }
}
// </vc-code>

fn main() {
}

}