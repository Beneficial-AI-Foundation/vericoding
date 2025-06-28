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
        n * fact((n - 1) as nat)
    }
}

fn factorial(n: nat) -> (res: nat)
    ensures
        res == fact(n)
    decreases n
{
    if n == 0 {
        1nat
    } else {
        let prev = factorial((n - 1) as nat);
        let result = n * prev;
        proof {
            assert(prev == fact((n - 1) as nat));
            assert(fact(n) == n * fact((n - 1) as nat));
            assert(result == n * prev);
            assert(result == n * fact((n - 1) as nat));
            assert(result == fact(n));
        }
        result
    }
}

}