use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn CalcPower(n: nat) -> (p: nat)
    ensures
        p == 2*n
{
    2 * n
}

}

The changes I made:

This should verify correctly since the function body `2 * n` exactly matches the specification `p == 2*n`.