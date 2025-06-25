// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn UpWhileNotEqual(N: int) -> (i: int)
    requires
        0 <= N
    ensures
        i == N
{
    return 0;
}

}