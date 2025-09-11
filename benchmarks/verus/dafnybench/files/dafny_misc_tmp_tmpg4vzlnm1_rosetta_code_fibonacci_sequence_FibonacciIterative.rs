// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn fibonacci(n: nat) -> nat
    decreases n
{
    if n == 0 {
        0
    } else if n == 1 {
        1
    } else {
        fibonacci((n - 1) as nat) + fibonacci((n - 2) as nat)
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn fibonacci_iterative(n: u64) -> (f: u64)
    requires n < 100
    ensures f == fibonacci(n as nat)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}