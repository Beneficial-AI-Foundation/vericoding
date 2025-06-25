use vstd::prelude::*;

verus! {

// Função recursiva da potência
spec fn Potencia(x: nat, y: nat) -> nat {
    if y == 0 {
        1
    } else {
        x * Potencia(x, y - 1)
    }
}

// Quero agora implementar como uma função não recursiva
pub fn Pot(x: nat, y: nat) -> (r: nat)
    ensures r == Potencia(x, y)
{
}

}