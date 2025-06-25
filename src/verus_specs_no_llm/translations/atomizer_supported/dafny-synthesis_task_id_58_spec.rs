// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn HasOppositeSign(a: int, b: int) -> (result: bool)
    ensures result <==> (a < 0 and b > 0) or (a > 0 and b < 0)
{
}

}