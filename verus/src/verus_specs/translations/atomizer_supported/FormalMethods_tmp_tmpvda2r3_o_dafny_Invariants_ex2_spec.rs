use vstd::prelude::*;

verus! {

spec fn Potencia(x: nat, y: nat) -> nat
    decreases y
{
    if y == 0 {
        1
    } else {
        x * Potencia(x, (y - 1) as nat)
    }
}

pub fn Pot(x: nat, y: nat) -> (r: nat)
    ensures r == Potencia(x, y)
{
}

}