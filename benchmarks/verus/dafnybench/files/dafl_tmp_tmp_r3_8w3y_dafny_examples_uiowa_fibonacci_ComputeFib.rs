use vstd::prelude::*;

verus! {

spec fn fib(n: nat) -> nat
    decreases n
{
    if n == 0 { 0 }
    else if n == 1 { 1 }
    else { fib((n - 1) as nat) + fib((n - 2) as nat) }
}

fn ComputeFib(n: usize) -> (f: usize)
    ensures f == fib(n as nat)
{
    assume(false);
    unreached()
}

}
fn main() {}