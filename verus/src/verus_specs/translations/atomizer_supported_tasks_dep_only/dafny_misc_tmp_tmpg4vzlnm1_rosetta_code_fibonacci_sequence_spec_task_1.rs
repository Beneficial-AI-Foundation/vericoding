use vstd::prelude::*;

verus! {

spec fn fibonacci(n: nat) -> nat {
    match n {
        0 => 0,
        1 => 1,
        _ => fibonacci((n - 1) as nat) + fibonacci((n - 2) as nat),
    }
}

pub fn fibonacci_iterative(n: nat) -> (f: nat)
    ensures f == fibonacci(n)
{
}

}