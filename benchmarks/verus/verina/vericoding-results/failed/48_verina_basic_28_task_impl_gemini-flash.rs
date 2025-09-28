// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): No changes needed in this section as it is a spec function previously added by LLM and is not the cause of the current error. */
spec fn is_prime_divisor(n: nat, k: nat) -> bool {
    k < n && n % k == 0
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
/* code modified by LLM (iteration 5): The error indicated `i = (i + 2) as nat;` was problematic because `(i + 2)` as `int` was being cast to `nat` in executable code. While `i` is a `nat` in the invariant, in executable code, `i` needs to be an `int` so that the operations `i+2` are `int` operations. The fix is to change the type of `i` to `usize` for executable code, since it needs to be an executable type that can be cast to `nat` within ghost contexts like the invariant, and `usize` is an appropriate unsigned integer type for loop counters. All arithmetic operations on `i` will thus be `usize` operations. */
{
    if n == 2 {
        true
    } else if n % 2 == 0 {
        false
    } else {
        let mut i: usize = 3; // Change 'i' to usize for executable code
        let mut result: bool = true;
        while (i as nat) * (i as nat) <= n // Cast `i` to `nat` for the comparison to `n`
            invariant (
                result == forall|k: nat| (2 <= k && k < (i as nat) && k % (2 as nat) != 0) ==> n % k != 0,
                (i as nat) % (2 as nat) == 1,
                (i as nat) >= 3,
                (i as nat) <= (n + 1) as nat,
            ),
            decreases (n - (i as nat)) as int
        {
            if n % (i as nat) == 0 { // Cast `i` to `nat` for the modulo operation
                result = false;
                break;
            }
            i = i + 2; // 'i' is now a usize, direct addition is fine
        }
        result
    }
}
// </vc-code>

}
fn main() {}