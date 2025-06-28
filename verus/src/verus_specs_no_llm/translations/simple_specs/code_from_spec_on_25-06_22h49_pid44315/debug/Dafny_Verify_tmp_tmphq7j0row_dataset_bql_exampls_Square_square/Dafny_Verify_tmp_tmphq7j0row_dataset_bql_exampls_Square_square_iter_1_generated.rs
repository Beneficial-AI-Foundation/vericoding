// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn square(n: int) -> (r: int)
    requires
        0 <= n
    ensures
        r == n*n
{
    return n * n;
}

}