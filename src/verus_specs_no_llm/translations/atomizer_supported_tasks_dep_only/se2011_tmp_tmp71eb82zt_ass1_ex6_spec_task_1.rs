// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn Ceiling7(n: nat) -> (k: nat)
    requires n >= 0
    ensures k == n-(n%7)
{
}

}