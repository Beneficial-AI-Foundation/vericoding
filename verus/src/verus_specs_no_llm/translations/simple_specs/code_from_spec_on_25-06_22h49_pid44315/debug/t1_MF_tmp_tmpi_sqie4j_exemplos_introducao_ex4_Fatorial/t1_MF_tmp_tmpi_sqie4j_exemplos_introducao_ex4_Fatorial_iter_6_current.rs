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
        proof {
            assert(Fat(0) == 1);
        }
        1
    } else {
        let prev = Fatorial(n - 1);
        proof {
            assert(prev == Fat(n - 1));
            assert(Fat(n) == n * Fat(n - 1));
            assert(n * prev == n * Fat(n - 1));
            assert(n * prev == Fat(n));
        }
        n * prev
    }
}

}