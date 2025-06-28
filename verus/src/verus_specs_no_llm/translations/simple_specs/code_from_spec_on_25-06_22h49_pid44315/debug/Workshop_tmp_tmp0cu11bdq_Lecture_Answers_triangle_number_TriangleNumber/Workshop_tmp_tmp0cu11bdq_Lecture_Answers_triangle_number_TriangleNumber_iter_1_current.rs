// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn TriangleNumber(N: int) -> (t: int)
    requires
        N >= 0
    ensures
        t == N * (N + 1) / 2
{
    N * (N + 1) / 2
}

}