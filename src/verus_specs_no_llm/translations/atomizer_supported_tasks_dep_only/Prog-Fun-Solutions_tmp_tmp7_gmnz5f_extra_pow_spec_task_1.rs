// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn Pow(a: nat, n: nat) -> (y: nat)
    ensures y == pow(a, n)
{
}

}