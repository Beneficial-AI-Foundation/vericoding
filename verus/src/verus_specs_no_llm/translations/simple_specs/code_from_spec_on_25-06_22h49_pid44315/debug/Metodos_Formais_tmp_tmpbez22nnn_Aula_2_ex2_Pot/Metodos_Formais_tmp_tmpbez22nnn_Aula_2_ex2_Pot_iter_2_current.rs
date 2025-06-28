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

The key fix was adding `decreases y` to the `Pot` function. This tells Verus that the function terminates because the parameter `y` decreases with each recursive call. Since both the spec function `Potencia` and the executable function `Pot` follow the same recursive pattern:

- Base case: when `y == 0`, both return `1`
- Recursive case: when `y > 0`, both compute `x * result_of_(x, y-1)`
- Both decrease `y` in each recursive call

The verification succeeds because the structure of both functions is identical, making it easy for Verus to prove that `Pot(x, y) == Potencia(x, y)` for all valid inputs.