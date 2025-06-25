// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn sumOdds(n: nat) -> (sum: nat)
    requires n > 0;
    ensures sum == n * n;
{
}

}