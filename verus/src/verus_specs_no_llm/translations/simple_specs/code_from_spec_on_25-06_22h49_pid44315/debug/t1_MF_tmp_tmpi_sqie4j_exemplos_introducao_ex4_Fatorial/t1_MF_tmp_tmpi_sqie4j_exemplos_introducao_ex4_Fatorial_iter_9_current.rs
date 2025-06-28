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
        n * Fat((n - 1) as nat)
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
        proof {
            assert(n > 0);
            assert((n - 1) >= 0);
        }
        let prev = Fatorial((n - 1) as nat);
        proof {
            assert(prev == Fat((n - 1) as nat));
            assert(Fat(n) == n * Fat((n - 1) as nat));
            assert(n * prev == n * Fat((n - 1) as nat));
            assert(n * prev == Fat(n));
        }
        n * prev
    }
}

}