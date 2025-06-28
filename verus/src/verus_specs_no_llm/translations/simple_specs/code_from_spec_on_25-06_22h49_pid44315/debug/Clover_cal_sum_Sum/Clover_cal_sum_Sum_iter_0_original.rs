// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Sum(N: int) -> (s: int)
    requires
        N >= 0
    ensures
        s == N * (N + 1) / 2
{
    return 0;
}

}