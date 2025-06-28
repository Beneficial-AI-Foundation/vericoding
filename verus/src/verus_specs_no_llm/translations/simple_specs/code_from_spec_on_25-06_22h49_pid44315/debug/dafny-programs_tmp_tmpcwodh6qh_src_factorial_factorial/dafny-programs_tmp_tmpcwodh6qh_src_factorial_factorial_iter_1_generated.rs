// Translated from Dafny
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
{
    if n == 0 {
        1
    } else {
        let prev = factorial((n - 1) as nat);
        n * prev
    }
}

}