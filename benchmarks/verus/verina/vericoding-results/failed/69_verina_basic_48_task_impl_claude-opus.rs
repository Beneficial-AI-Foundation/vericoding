// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_perfect_square(n: nat) -> bool {
    exists|i: nat| #[trigger] (i * i) == n
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn is_perfect_square_fn(n: u64) -> (result: bool)
    ensures result <==> is_perfect_square(n as nat),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Removed invalid trigger from forall in invariant */
    let mut i: u64 = 0;
    while i <= n
        invariant
            i <= n + 1,
            forall|j: nat| j < i ==> (j * j) != n,
        decreases n - i + 1,
    {
        if i * i == n {
            assert(is_perfect_square(n as nat)) by {
                assert((i as nat) * (i as nat) == n);
            }
            return true;
        }
        if i * i > n {
            assert(!is_perfect_square(n as nat)) by {
                assert forall|k: nat| (k * k) != n by {
                    if k < i {
                        assert((k * k) != n);
                    } else {
                        assert(k >= i);
                        assert((k * k) >= (i * i));
                        assert((k * k) > n);
                    }
                }
            }
            return false;
        }
        i = i + 1;
    }
    false
}
// </vc-code>

}
fn main() {}