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
        assert(n >= 2);
        let fib_n_minus_1 = Fib((n - 1) as nat);
        let fib_n_minus_2 = Fib((n - 2) as nat);
        let result = fib_n_minus_1 + fib_n_minus_2;
        assert(result == fib(n - 1) + fib(n - 2));
        result
    }
}

}