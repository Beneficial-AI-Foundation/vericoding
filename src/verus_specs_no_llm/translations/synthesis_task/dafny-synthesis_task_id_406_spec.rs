// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn IsOdd(n: int) -> (result: bool)
    ensures result <==> n % 2 == 1
{
}

}