use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Mult(x: nat, y: nat) -> (r: nat)
    ensures
        r == x * y
{
    x * y
}

}