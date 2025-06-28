use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn Potencia(x: nat, y: nat) -> nat
    decreases y
{
    if y == 0 {
        1
    } else {
        x * Potencia(x, y - 1)
    }
}

fn Pot(x: nat, y: nat) -> (r: nat)
    ensures
        r == Potencia(x, y)
    decreases y
{
    if y == 0 {
        1
    } else {
        let sub_result = Pot(x, y - 1);
        x * sub_result
    }
}

}