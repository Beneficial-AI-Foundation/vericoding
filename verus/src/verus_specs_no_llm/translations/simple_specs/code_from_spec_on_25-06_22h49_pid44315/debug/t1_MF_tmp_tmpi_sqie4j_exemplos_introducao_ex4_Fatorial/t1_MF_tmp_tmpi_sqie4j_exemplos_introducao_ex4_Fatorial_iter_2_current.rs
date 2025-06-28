use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn Fat(n: nat) -> nat
    decreases n
{
    if n == 0 {
        1
    } else {
        n * Fat(n - 1)
    }
}

fn Fatorial(n: nat) -> (r: nat)
    ensures
        r == Fat(n)
    decreases n
{
    if n == 0 {
        1
    } else {
        n * Fatorial(n - 1)
    }
}

}