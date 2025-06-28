// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn ComputeFactorial(n: int) -> (u: int)
    requires
        1 <= n
    ensures
        u == Factorial(n)
{
    return 0;
}

}