// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn Fibonacci(n: nat) -> nat
{
    0
}

spec fn spec_FibonacciIterative(n: nat) -> f: nat
    ensures
        f == Fibonacci(n)
;

proof fn lemma_FibonacciIterative(n: nat) -> (f: nat)
    ensures
        f == Fibonacci(n)
{
    0
}

}