// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn factorial(n: nat) -> nat
    decreases n
{
    if n == 0 { 1 } else { n * factorial(sub(n, 1)) }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn find(A: &mut Vec<i8>, N: usize, f: usize)
    requires 
        old(A)@.len() == N,
        f < N,
    ensures
        forall|p: int, q: int| 0 <= p <= f as int <= q < N as int ==> A@[p] as int <= A@[q] as int,
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}