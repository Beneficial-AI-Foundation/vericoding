// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn Sum(n: nat) -> (s: int)
    ensures s == sum(n)
{
}

}