// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn Max(x: nat, y: nat) -> (r: nat)
    ensures (r >= x and r >=y),
            (r == x or r == y)
{
}

}