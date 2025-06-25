// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn IsEven(n: int) -> (result: bool)
    ensures result <==> n % 2 == 0
{
}

}