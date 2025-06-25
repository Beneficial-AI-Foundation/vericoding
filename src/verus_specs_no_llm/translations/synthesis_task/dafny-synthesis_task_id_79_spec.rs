// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn IsLengthOdd(s: String) -> (result: bool)
    ensures result <==> s.len() % 2 == 1
{
}

}