// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
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