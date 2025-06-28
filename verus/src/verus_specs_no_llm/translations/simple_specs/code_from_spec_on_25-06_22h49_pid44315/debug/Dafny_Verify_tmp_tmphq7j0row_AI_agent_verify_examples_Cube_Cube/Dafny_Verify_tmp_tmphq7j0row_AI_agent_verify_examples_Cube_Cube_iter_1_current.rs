// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Cube(n: nat) -> (c: nat)
    ensures
        c == n * n * n
{
    return n * n * n;
}

}