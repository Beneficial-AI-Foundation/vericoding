// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_perfect_square(n: nat) -> bool {
    exists|i: nat| #[trigger] (i * i) == n
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed spec function syntax and added proper lemmas */
spec fn sqrt_upper_bound(n: nat) -> nat {
    n + 1
}

proof fn sqrt_properties(n: nat)
    ensures forall|i: nat| i * i == n ==> i <= n
{
}

proof fn perfect_square_witness(n: nat, i: nat)
    requires i * i == n
    ensures is_perfect_square(n)
{
}

proof fn no_perfect_square_witness(n: nat)
    requires forall|i: nat| i <= n ==> i * i != n
    ensures !is_perfect_square(n)
{
}
// </vc-helpers>

// <vc-spec>
fn is_perfect_square_fn(n: u64) -> (result: bool)
    ensures result <==> is_perfect_square(n as nat),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fixed invariant syntax with proper braces */
{
    let mut i: u64 = 0;
    while i <= n
        invariant forall|j: nat| j < i ==> j * j != n as nat
        invariant i * i <= n || i > n
    {
        if i * i == n {
            proof {
                perfect_square_witness(n as nat, i as nat);
            }
            return true;
        }
        if i * i > n {
            proof {
                no_perfect_square_witness(n as nat);
            }
            return false;
        }
        i = i + 1;
    }
    proof {
        no_perfect_square_witness(n as nat);
    }
    false
}
// </vc-code>

}
fn main() {}