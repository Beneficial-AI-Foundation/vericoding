use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn fib(n: nat) -> nat
    decreases n
{
    if n == 0 {
        0
    } else if n == 1 {
        1
    } else {
        fib(n - 1) + fib(n - 2)
    }
}

fn Fib(n: nat) -> (r: nat)
    ensures
        r == fib(n)
    decreases n
{
    if n == 0 {
        0
    } else if n == 1 {
        1
    } else {
        let prev2 = Fib(n - 2);
        let prev1 = Fib(n - 1);
        prev1 + prev2
    }
}

}