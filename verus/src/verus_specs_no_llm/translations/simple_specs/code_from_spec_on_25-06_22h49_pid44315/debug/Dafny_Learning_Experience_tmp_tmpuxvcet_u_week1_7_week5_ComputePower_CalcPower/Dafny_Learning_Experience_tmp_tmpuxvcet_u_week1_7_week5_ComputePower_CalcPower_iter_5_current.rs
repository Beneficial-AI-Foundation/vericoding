use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn CalcPower(n: nat) -> (p: nat)
    ensures
        p == 2*n
{
    let result = 2*n;
    assert(result == 2*n);
    result
}

}