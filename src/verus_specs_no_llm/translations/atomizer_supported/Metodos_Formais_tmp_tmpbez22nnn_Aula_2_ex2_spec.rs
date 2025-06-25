// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn Pot(x: nat, y: nat) -> (r: nat)
    ensures r == Potencia(x,y)
{
}

}