// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn ComputeFact(n: int) -> (f: int)
    requires
        n >=0
    ensures
        f== factorial(n)
{
    return 0;
}

}