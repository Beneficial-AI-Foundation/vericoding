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

fn AdditiveFactorial(n: nat) -> (u: nat)
    ensures
        u == Factorial(n)
{
    return 0;
}

}