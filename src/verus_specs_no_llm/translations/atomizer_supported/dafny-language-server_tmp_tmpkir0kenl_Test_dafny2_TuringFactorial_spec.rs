// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn ComputeFactorial(n: int) -> (u: int)
    requires 1 <= n;
    ensures u == Factorial(n);
{
}

}