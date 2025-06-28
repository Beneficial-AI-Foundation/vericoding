use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Ceiling7(n: nat) -> (k: nat)
    ensures
        k == n - (n % 7)
{
    if n % 7 == 0 {
        n
    } else {
        n + (7 - (n % 7))
    }
}

}