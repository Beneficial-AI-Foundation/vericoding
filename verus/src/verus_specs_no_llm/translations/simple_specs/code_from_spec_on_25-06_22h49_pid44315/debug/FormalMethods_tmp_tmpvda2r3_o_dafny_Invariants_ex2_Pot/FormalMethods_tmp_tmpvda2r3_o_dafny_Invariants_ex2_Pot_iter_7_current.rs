use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn Potencia(x: nat, y: nat) -> nat 
    decreases y
{
    if y == 0 {
        1nat
    } else {
        x * Potencia(x, (y - 1) as nat)
    }
}

fn Pot(x: nat, y: nat) -> (r: nat)
    ensures
        r == Potencia(x, y),
    decreases y
{
    if y == 0 {
        1nat
    } else {
        let sub_result = Pot(x, (y - 1) as nat);
        x * sub_result
    }
}

}