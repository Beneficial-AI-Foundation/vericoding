// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn ContainsK(s: Seq<int>, k: int) -> (result: bool)
    ensures result <==> k in s
{
}

}