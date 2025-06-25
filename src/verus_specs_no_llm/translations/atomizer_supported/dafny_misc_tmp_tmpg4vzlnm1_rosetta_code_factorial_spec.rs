// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn IterativeFactorial(n: nat) -> (result: nat)
    ensures result == Factorial(n)
{
}

}