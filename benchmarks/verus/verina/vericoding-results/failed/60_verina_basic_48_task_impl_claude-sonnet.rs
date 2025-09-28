// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_perfect_square(n: nat) -> bool {
    exists|i: nat| #[trigger] (i * i) == n
}
// </vc-preamble>

// <vc-helpers>
proof fn lemma_sqrt_bound(n: u64)
    ensures
        n < (n as nat + 1) * (n as nat + 1),
{
    let n_nat = n as nat;
    assert((n_nat + 1) * (n_nat + 1) == n_nat * n_nat + 2 * n_nat + 1);
    assert(n_nat < n_nat * n_nat + 2 * n_nat + 1);
}

proof fn lemma_perfect_square_bound(n: nat, i: nat)
    requires i * i == n,
    ensures i <= n,
{
    if i > n {
        assert(i >= n + 1);
        assert(i * i >= (n + 1) * (n + 1)) by {
            assert(i >= n + 1);
        }
        assert((n + 1) * (n + 1) == n * n + 2 * n + 1) by {
            assert((n + 1) * (n + 1) == n * n + n + n + 1);
        }
        assert(i * i >= n * n + 2 * n + 1) by {
            assert(i * i >= (n + 1) * (n + 1));
            assert((n + 1) * (n + 1) == n * n + 2 * n + 1);
        }
        assert(n * n + 2 * n + 1 > n) by {
            assert(n * n >= 0);
            assert(2 * n >= 0);
            assert(n * n + 2 * n + 1 >= 2 * n + 1);
            assert(2 * n + 1 > n);
        }
        assert(i * i > n);
        assert(false) by {
            assert(i * i == n);
            assert(i * i > n);
        }
    }
}

/* helper modified by LLM (iteration 5): fixed arithmetic and overflow handling */
proof fn lemma_no_square_exists(n: nat, max_checked: nat)
    requires
        forall|j: nat| #[trigger] (j * j) == (j * j) && j <= max_checked ==> j * j != n,
        max_checked * max_checked <= n,
        (max_checked + 1) * (max_checked + 1) > n,
    ensures !is_perfect_square(n)
{
    assert forall|k: nat| #[trigger] (k * k) == n implies false by {
        if k <= max_checked {
            assert(k * k != n);
        } else {
            assert(k >= max_checked + 1);
            assert(k * k >= (max_checked + 1) * (max_checked + 1));
            assert((max_checked + 1) * (max_checked + 1) > n);
            assert(k * k > n);
            assert(k * k != n);
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn is_perfect_square_fn(n: u64) -> (result: bool)
    ensures result <==> is_perfect_square(n as nat),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed overflow checks and logic */
    if n == 0 {
        return true;
    }
    
    let mut i: u64 = 0;
    while i <= n
        invariant
            forall|j: nat| #[trigger] (j * j) == (j * j) && j < i ==> j * j != n as nat,
            i <= n + 1,
        decreases n + 1 - i
    {
        // Check for overflow before multiplication
        if i > 0 && i > u64::MAX / i {
            return false;
        }
        
        let i_squared = i * i;
        
        if i_squared == n {
            proof {
                assert(is_perfect_square(n as nat)) by {
                    assert((i as nat) * (i as nat) == n as nat);
                }
            }
            return true;
        }
        
        if i_squared > n {
            proof {
                if i > 0 {
                    lemma_no_square_exists(n as nat, (i - 1) as nat);
                }
            }
            return false;
        }
        
        i = i + 1;
    }
    
    proof {
        lemma_no_square_exists(n as nat, n as nat);
    }
    false
}
// </vc-code>

}
fn main() {}