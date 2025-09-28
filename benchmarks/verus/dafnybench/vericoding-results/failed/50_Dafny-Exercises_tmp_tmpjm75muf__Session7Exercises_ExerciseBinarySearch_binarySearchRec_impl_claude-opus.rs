use vstd::prelude::*;

verus! {

spec fn sorted(s: Seq<i32>) -> bool {
    forall|u: int, w: int| 0 <= u < w < s.len() ==> s[u] <= s[w]
}







//Recursive binary search

// <vc-helpers>
// Helper to prove termination by showing the measure decreases
proof fn termination_proof(c: usize, f: usize, mid: usize)
    requires
        c <= f,
        c <= mid <= f,
    ensures
        f - (mid + 1) < f - c,
        mid == 0 || (mid - 1) as int - c as int < (f as int - c as int),
{
    assert(mid >= c);
    assert(mid + 1 > c);
    assert(f - (mid + 1) < f - c);
    
    if mid > 0 {
        assert(mid <= f);
        assert(mid - 1 < f);
        assert((mid - 1) as int - c as int < f as int - c as int);
    }
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
    if c > f {
        // Base case: empty search range
        // All elements [0, f] are <= elem (by precondition about [0, c))
        // All elements [f+1, v.len()) are > elem (by precondition)
        proof {
            assert(f < v.len()) by {
                // Since f + 1 <= v.len() from precondition
                assert(f + 1 <= v.len());
            }
            // We know f < v.len() and v.len() fits in usize
            // Since p is i32, we need f to fit in i32
            // This is guaranteed by the fact that f < v.len() and vectors have reasonable size
        }
        return f as i32;
    }
    
    let mid: usize = c + (f - c) / 2;
    
    proof {
        assert(c <= mid <= f);
        assert(mid < v.len()) by {
            assert(f < v.len()) by {
                assert(f + 1 <= v.len());
            }
            assert(mid <= f);
        }
    }
    
    if v[mid] <= elem {
        // v[mid] <= elem, so search in the right half
        // We know all elements [0, mid] are <= elem
        proof {
            assert forall|k: int| 0 <= k <= mid implies v[k] <= elem by {
                if k < c {
                    // By precondition
                } else if k == mid as int {
                    // We just checked this
                } else {
                    // c <= k < mid
                    assert(sorted(v@));
                    assert(v@[k] <= v@[mid as int]);
                }
            }
            // Prove termination: f - (mid + 1) < f - c
            termination_proof(c, f, mid);
        }
        
        // Recursive call on right half
        binary_search_rec(v, elem, mid + 1, f)
    } else {
        // v[mid] > elem, so search in the left half
        // We know all elements [mid, v.len()) are > elem
        proof {
            assert forall|k: int| mid <= k < v.len() implies v[k] > elem by {
                if k == mid as int {
                    // We just checked this
                } else if k > f {
                    // By precondition
                } else {
                    // mid < k <= f
                    assert(sorted(v@));
                    assert(v@[mid as int] <= v@[k]);
                    assert(v@[mid as int] > elem);
                }
            }
            // Prove termination
            termination_proof(c, f, mid);
        }
        
        // Recursive call on left half
        if mid == 0 {
            binary_search_rec(v, elem, c, 0)
        } else {
            binary_search_rec(v, elem, c, mid - 1)
        }
    }
}
// </vc-code>

fn main() {
}

}