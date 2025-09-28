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
    /* code modified by LLM (iteration 5): added #[trigger] to quantifier to resolve trigger inference error */
    let mut i: u64 = 0;
    let max_i: u64 = 4294967295;
    while i <= max_i && (i as u128) * (i as u128) <= (n as u128)
        invariant
            0 <= i && i <= max_i,
            forall |k: nat| 0 <= k < i ==> (#[trigger] ((k as nat) * (k as nat))) != n as nat,
        decreases (max_i as int - i as int)
    {
        if (i as u128) * (i as u128) == (n as u128) {
            return true;
        }
        if i == max_i {
            break;
        }
        i += 1;
    }
    return false;
}
// </vc-code>

}
fn main() {}