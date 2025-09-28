// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_perfect_square(n: nat) -> bool {
    exists|i: nat| #[trigger] (i * i) == n
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): removed unnecessary helper lemma */
// </vc-helpers>

// <vc-spec>
fn is_perfect_square_fn(n: u64) -> (result: bool)
    ensures result <==> is_perfect_square(n as nat),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): fixed overflow checks and postcondition proof */
{
    if n == 0 {
        proof {
            assert(0nat * 0nat == 0nat);
        }
        return true;
    }
    
    let mut i: u64 = 0;
    while i <= n
        invariant
            i <= n + 1,
            forall|j: nat| j < i as nat ==> #[trigger] (j * j) != n as nat,
            i * i <= u64::MAX,
        decreases n + 1 - i,
    {
        if i as u128 * i as u128 == n as u128 {
            proof {
                assert(i as nat * i as nat == n as nat);
            }
            return true;
        }
        if i as u128 * i as u128 > n as u128 {
            proof {
                assert(forall|k: nat| k < i as nat ==> #[trigger] (k * k) != n as nat);
                assert(i as nat * i as nat > n as nat);
                assert(forall|k: nat| k >= i as nat ==> k * k >= i as nat * i as nat);
                assert(forall|k: nat| k >= i as nat ==> #[trigger] (k * k) > n as nat);
                assert(!is_perfect_square(n as nat));
            }
            return false;
        }
        proof {
            assert(i as nat * i as nat != n as nat);
        }
        if i == n {
            break;
        }
        i = i + 1;
    }
    
    proof {
        assert(i == n + 1 || i == n);
        assert(forall|j: nat| j <= n as nat ==> #[trigger] (j * j) != n as nat);
        assert(forall|k: nat| k > n as nat ==> #[trigger] (k * k) > n as nat);
        assert(!is_perfect_square(n as nat));
    }
    false
}
// </vc-code>

}
fn main() {}