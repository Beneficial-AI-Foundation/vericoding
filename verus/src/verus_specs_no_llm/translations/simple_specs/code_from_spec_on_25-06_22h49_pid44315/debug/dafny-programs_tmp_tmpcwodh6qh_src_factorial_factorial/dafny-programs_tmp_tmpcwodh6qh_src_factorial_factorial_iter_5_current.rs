use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn fact(n: nat) -> nat
    decreases n
{
    if n == 0 {
        1
    } else {
        n * fact(n - 1)
    }
}

fn factorial(n: nat) -> (res: nat)
    ensures
        res == fact(n)
    decreases n
{
    if n == 0 {
        1
    } else {
        let prev = factorial(n - 1);
        let result = n * prev;
        proof {
            assert(prev == fact(n - 1));
            assert(result == n * prev);
            assert(fact(n) == n * fact(n - 1));
            assert(result == n * fact(n - 1));
            assert(result == fact(n));
        }
        result
    }
}

}