// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn factorial(n: nat) -> (res: nat)
    ensures res == fact(n)
{
}

}