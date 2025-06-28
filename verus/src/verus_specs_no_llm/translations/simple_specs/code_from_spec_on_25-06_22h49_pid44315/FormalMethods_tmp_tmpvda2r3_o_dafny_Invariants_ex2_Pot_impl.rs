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
        r == Potencia(x, y),
    decreases y
{
    if y == 0 {
        proof {
            assert(Potencia(x, 0) == 1);
        }
        1
    } else {
        let sub_result = Pot(x, (y - 1) as nat);
        proof {
            assert(sub_result == Potencia(x, (y - 1) as nat));
            assert(y >= 1);
            assert((y - 1) as nat == y - 1);
            assert(sub_result == Potencia(x, y - 1));
        }
        let result = x * sub_result;
        proof {
            assert(result == x * sub_result);
            assert(result == x * Potencia(x, y - 1));
            assert(Potencia(x, y) == x * Potencia(x, y - 1)) by {
                assert(y != 0);
            }
            assert(result == Potencia(x, y));
        }
        result
    }
}

}