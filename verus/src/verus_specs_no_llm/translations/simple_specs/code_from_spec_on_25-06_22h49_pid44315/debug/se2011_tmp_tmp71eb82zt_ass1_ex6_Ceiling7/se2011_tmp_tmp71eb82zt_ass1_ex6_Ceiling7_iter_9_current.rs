use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Ceiling7(n: nat) -> (k: nat)
    ensures
        k % 7 == 0,
        k >= n,
        k < n + 7
{
    if n % 7 == 0 {
        n
    } else {
        n + (7 - (n % 7))
    }
}

}