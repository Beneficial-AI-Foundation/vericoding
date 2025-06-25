// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn CenteredHexagonalNumber(n: nat) -> (result: nat)
    requires n >= 0
    ensures result == 3 * n * (n - 1) + 1
{
}

}