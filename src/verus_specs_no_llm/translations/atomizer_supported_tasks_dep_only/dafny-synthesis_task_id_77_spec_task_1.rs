// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn IsDivisibleBy11(n: int) -> (result: bool)
    ensures result <==> n % 11 == 0
{
}

}