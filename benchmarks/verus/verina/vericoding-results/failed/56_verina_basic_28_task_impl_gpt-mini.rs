// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): trivial monotonicity lemma */
fn lemma_two_le_implies_one(n: nat)
    requires
        n >= 2,
    ensures
        n >= 1,
{
    assert(n >= 2);
    assert(n >= 1);
}

// </vc-helpers>

// <vc-spec>
fn is_prime(n: nat) -> (result: bool)
    requires n >= 2,
    ensures
        result ==> forall|k: nat| 2 <= k < n ==> #[trigger] (n % k) != 0,
        !result ==> exists|k: nat| 2 <= k < n && #[trigger] (n % k) == 0,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): iterative primality check with loop invariant */
    let two: nat = 2;
    let mut k: nat = two;
    while k < n
        invariant
            forall|j: nat| two <= j && j < k ==> n % j != 0,
        decreases
            n - k
    {
        if n % k == 0 {
            return false;
        }
        k = k + 1;
    }
    true
}

// </vc-code>

}
fn main() {}