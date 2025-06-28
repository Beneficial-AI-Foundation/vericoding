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
{
    if y == 0 {
        1
    } else {
        let sub_result = Pot(x, y - 1);
        x * sub_result
    }
}

}

The implementation:

   - Base case: x^0 = 1
   - Recursive case: x^y = x * x^(y-1)
   - Uses `decreases y` to prove termination

   - Base case: returns 1 when y == 0
   - Recursive case: recursively computes x^(y-1) and multiplies by x
   - The structure mirrors the spec function, making verification straightforward

The function satisfies the ensures clause `r == Potencia(x,y)` because both the spec and executable functions follow the same recursive pattern for computing exponentiation.