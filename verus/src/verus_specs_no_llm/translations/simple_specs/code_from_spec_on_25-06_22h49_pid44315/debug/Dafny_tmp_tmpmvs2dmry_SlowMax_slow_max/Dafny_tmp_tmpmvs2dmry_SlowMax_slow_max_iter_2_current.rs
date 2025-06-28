use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn max(a: nat, b: nat) -> nat {
    if a >= b { a } else { b }
}

fn slow_max(a: nat, b: nat) -> (z: nat)
    ensures
        z == max(a, b)
{
    if a >= b {
        a
    } else {
        b
    }
}

}