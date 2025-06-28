// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn square0(n: nat) -> (sqn: nat)
    ensures
        sqn == n*n
{
    return n * n;
}

}