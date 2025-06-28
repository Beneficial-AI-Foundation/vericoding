// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Pot(x: nat, y: nat) -> (r: nat)
    ensures
        r == Potencia(x,y)
{
    return 0;
}

}