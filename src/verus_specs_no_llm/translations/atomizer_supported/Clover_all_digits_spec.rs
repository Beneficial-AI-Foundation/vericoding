// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn allDigits(s: String) -> (result: bool)
    ensures result <==> (forall|i: int| 0 <= i < s.len() ==> s[i] in "0123456789")
{
}

}