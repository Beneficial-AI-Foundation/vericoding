// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn fib(n: nat) -> nat
    decreases n
{
    if n == 0 { 0 }
    else if n == 1 { 1 }
    else { fib((n - 1) as nat) + fib((n - 2) as nat) }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn ComputeFib(n: usize) -> (f: usize)
    ensures f == fib(n as nat)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}