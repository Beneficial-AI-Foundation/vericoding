// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn cube(n: int) -> int {
        n * n * n
}
    
    // </vc-preamble>

// <vc-helpers>
proof fn lemma_cube_bounds(k: int)
    requires k >= 0
    ensures cube(k) >= 0
{
}

proof fn lemma_cube_monotonic(i: int, j: int)
    requires 0 <= i <= j
    ensures cube(i) <= cube(j)
{
    /* helper modified by LLM (iteration 5): fixed monotonicity proof with proper arithmetic reasoning */
    if i == j {
        assert(cube(i) == cube(j));
    } else {
        assert(i < j);
        assert(i * i <= j * j) by {
            if i == 0 {
                assert(i * i == 0);
                assert(j * j >= 0);
            } else {
                assert(i >= 0 && j >= i);
                assert(i * j <= j * j);
                assert(i * i <= i * j);
            }
        }
        assert(i * i * i <= j * j * j) by {
            assert(i <= j);
            assert(i * i <= j * j);
            assert((i * i) * i <= (j * j) * j) by {
                assert(i <= j);
                assert(i * i >= 0);
                assert(j * j >= 0);
            }
        }
    }
}

proof fn lemma_cube_upper_bound(k: int, n: int)
    requires k > n >= 0
    ensures cube(k) > n
{
    /* helper modified by LLM (iteration 5): simplified upper bound proof */
    assert(k >= n + 1);
    assert(k >= 1);
    assert(cube(k) >= cube(1)) by {
        lemma_cube_monotonic(1, k);
    }
    assert(cube(1) == 1);
    assert(cube(k) >= 1);
    if n == 0 {
        assert(cube(k) >= 1 > 0);
    } else {
        assert(k >= n + 1);
        assert(cube(k) >= cube(n + 1)) by {
            lemma_cube_monotonic(n + 1, k);
        }
        assert(cube(n + 1) > n) by {
            assert((n + 1) >= 1);
            assert((n + 1) * (n + 1) * (n + 1) >= n + 1);
            assert(n + 1 > n);
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn is_cube(n: u8) -> (r: bool)
    ensures r == exists|k: int| 0 <= k <= n as int && n as int == cube(k)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed overflow bounds and postcondition proof */
    let mut k = 0u64;
    let n_u64 = n as u64;
    
    while k <= n_u64
        invariant
            0 <= k <= n_u64 + 1,
            forall|i: int| 0 <= i < k as int ==> cube(i) < n as int,
        decreases n_u64 - k
    {
        // Check for potential overflow before computing cube
        if k > 6 { // 7^3 = 343 > 255
            proof {
                lemma_cube_upper_bound(k as int, n as int);
                assert(cube(k as int) > n as int);
                assert(forall|j: int| j >= k as int ==> cube(j) > n as int);
                assert(!exists|j: int| 0 <= j <= n as int && n as int == cube(j));
            }
            return false;
        }
        
        let k_cubed = k * k * k;
        if k_cubed == n_u64 {
            proof {
                let k_int = k as int;
                let n_int = n as int;
                assert(0 <= k_int <= n_int && n_int == cube(k_int));
                assert(exists|j: int| 0 <= j <= n_int && n_int == cube(j));
            }
            return true;
        }
        if k_cubed > n_u64 {
            proof {
                let k_int = k as int;
                let n_int = n as int;
                assert(cube(k_int) > n_int);
                lemma_cube_monotonic(k_int, n_int);
                assert(forall|j: int| j >= k_int ==> cube(j) >= cube(k_int));
                assert(forall|j: int| j >= k_int ==> cube(j) > n_int);
                assert(!exists|j: int| 0 <= j <= n_int && n_int == cube(j));
            }
            return false;
        }
        k = k + 1;
    }
    
    proof {
        assert(k == n_u64 + 1);
        assert(forall|i: int| 0 <= i <= n as int ==> cube(i) < n as int);
        assert(!exists|j: int| 0 <= j <= n as int && n as int == cube(j));
    }
    false
}
// </vc-code>


}

fn main() {}