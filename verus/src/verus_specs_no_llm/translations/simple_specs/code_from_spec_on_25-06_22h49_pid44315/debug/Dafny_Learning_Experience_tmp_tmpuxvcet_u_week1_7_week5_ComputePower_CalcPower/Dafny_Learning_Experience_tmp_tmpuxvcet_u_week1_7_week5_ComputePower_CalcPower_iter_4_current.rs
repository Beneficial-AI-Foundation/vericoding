use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn CalcPower(n: nat) -> (p: nat)
    ensures
        p == 2*n
{
    2*n
}

}