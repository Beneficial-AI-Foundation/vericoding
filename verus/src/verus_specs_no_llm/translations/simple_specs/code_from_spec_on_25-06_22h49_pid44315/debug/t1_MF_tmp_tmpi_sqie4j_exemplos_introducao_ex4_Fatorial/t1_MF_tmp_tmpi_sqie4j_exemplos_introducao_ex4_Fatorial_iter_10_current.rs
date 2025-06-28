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
        1
    } else {
        let prev = Fatorial((n - 1) as nat);
        n * prev
    }
}

}