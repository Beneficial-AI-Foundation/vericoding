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
        fib((n - 1) as nat) + fib((n - 2) as nat)
    }
}

fn Fib(n: nat) -> (r: nat)
    ensures
        r == fib(n)
{
    if n == 0 {
        0
    } else if n == 1 {
        1
    } else {
        let fib_n_minus_1 = Fib((n - 1) as nat);
        let fib_n_minus_2 = Fib((n - 2) as nat);
        fib_n_minus_1 + fib_n_minus_2
    }
}

}