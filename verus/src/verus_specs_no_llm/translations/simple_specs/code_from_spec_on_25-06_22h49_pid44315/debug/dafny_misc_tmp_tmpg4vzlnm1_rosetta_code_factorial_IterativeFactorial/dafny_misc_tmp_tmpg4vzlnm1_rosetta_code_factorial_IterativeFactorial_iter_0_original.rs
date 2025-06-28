// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn IterativeFactorial(n: nat) -> (result: nat)
    ensures
        result == Factorial(n)
{
    return 0;
}

}