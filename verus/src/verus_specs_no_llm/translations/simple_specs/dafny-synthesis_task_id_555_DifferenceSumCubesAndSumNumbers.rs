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

fn DifferenceSumCubesAndSumNumbers(n: int) -> (diff: int)
    requires
        n >= 0
    ensures
        diff == (n * n * (n + 1) * (n + 1)) / 4 - (n * (n + 1)) / 2
{
    return 0;
}

}